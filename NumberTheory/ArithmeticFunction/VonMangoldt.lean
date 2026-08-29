/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The von Mangoldt Function

In this file we define the von Mangoldt function: the function on natural numbers that returns
`log p` if the input can be expressed as `p^k` for a prime `p`.

## Main Results

The main definition for this file is

- `ArithmeticFunction.vonMangoldt`: The von Mangoldt function `Λ`.

We then prove the classical summation property of the von Mangoldt function in
`ArithmeticFunction.vonMangoldt_sum`, that `∑ i ∈ n.divisors, Λ i = Real.log n`, and use this
to deduce alternative expressions for the von Mangoldt function via Möbius inversion, see
`ArithmeticFunction.sum_moebius_mul_log_eq`.

## Notation

We use the standard notation `Λ` to represent the von Mangoldt function.
It is accessible in the locales `ArithmeticFunction` (like the notations for other arithmetic
functions) and also in the scope `ArithmeticFunction.vonMangoldt`.

-/

@[expose] public section

namespace ArithmeticFunction

open Finset Nat

open scoped ArithmeticFunction

/--
Definition of `log` / `log` 的定义

English:
definition log
  signature: : ArithmeticFunction Real
  body: ⟨fun n => Real.log n, by simp⟩

@[simp]

中文:
定义 log
  签名: : ArithmeticFunction 实数
  定义体: ⟨fun n => Real.log n, by simp⟩

@[simp]

Depends on / 依赖: Real.log
-/
noncomputable def log : ArithmeticFunction Real :=
  ⟨fun n => Real.log n, by simp⟩

@[simp]
/--
theorem `log_apply` / 定理 `log_apply`

English:
theorem log_apply
  given: {n : Nat}
  statement: log n = Real.log n
  proof: rfl

中文:
定理 log_apply
  条件: {n : 自然数}
  结论: log n = 实数.log n
  证明: rfl
-/
theorem log_apply {n : Nat} : log n = Real.log n :=
  rfl

/--
Definition of `vonMangoldt` / `vonMangoldt` 的定义

English:
definition vonMangoldt
  signature: : ArithmeticFunction Real
  body: ⟨fun n => if IsPrimePow n then Real.log (minFac n) else 0, if_neg not_isPrimePow_zero⟩

@[inherit_doc] scoped[ArithmeticFunction] notation "Λ" => ArithmeticFunction.vonMangoldt

@[inherit_doc] scoped[ArithmeticFunction.vonMangoldt] notation "Λ" =>
  ArithmeticFunction.vonMangoldt

中文:
定义 vonMangoldt
  签名: : ArithmeticFunction 实数
  定义体: ⟨fun n => if IsPrimePow n then Real.log (minFac n) else 0, if_neg not_isPrimePow_zero⟩

@[inherit_doc] scoped[ArithmeticFunction] notation "Λ" => ArithmeticFunction.vonMangoldt

@[inherit_doc] scoped[ArithmeticFunction.vonMangoldt] notation "Λ" =>
  ArithmeticFunction.vonMangoldt

Depends on / 依赖: IsPrimePow, Real.log, if_neg, minFac, not_isPrimePow_zero
-/
noncomputable def vonMangoldt : ArithmeticFunction Real :=
  ⟨fun n => if IsPrimePow n then Real.log (minFac n) else 0, if_neg not_isPrimePow_zero⟩

@[inherit_doc] scoped[ArithmeticFunction] notation "Λ" => ArithmeticFunction.vonMangoldt

@[inherit_doc] scoped[ArithmeticFunction.vonMangoldt] notation "Λ" =>
  ArithmeticFunction.vonMangoldt

/--
theorem `vonMangoldt_apply` / 定理 `vonMangoldt_apply`

English:
theorem vonMangoldt_apply
  given: {n : Nat}
  statement: Λ n = if IsPrimePow n then Real.log (minFac n) else 0
  proof: rfl

@[simp]

中文:
定理 vonMangoldt_apply
  条件: {n : 自然数}
  结论: Λ n = if IsPrimePow n then 实数.log (minFac n) else 0
  证明: rfl

@[simp]
-/
theorem vonMangoldt_apply {n : Nat} : Λ n = if IsPrimePow n then Real.log (minFac n) else 0 :=
  rfl

@[simp]
/--
theorem `vonMangoldt_apply_one` / 定理 `vonMangoldt_apply_one`

English:
theorem vonMangoldt_apply_one
  statement: Λ 1 = 0
  proof: by simp [vonMangoldt_apply]

@[simp]

中文:
定理 vonMangoldt_apply_one
  结论: Λ 1 = 0
  证明: by simp [vonMangoldt_apply]

@[simp]

Depends on / 依赖: vonMangoldt_apply
-/
theorem vonMangoldt_apply_one : Λ 1 = 0 := by simp [vonMangoldt_apply]

@[simp]
/--
theorem `vonMangoldt_nonneg` / 定理 `vonMangoldt_nonneg`

English:
theorem vonMangoldt_nonneg
  given: {n : Nat}
  statement: 0 <= Λ n
  proof: by
  rw [vonMangoldt_apply]
  split_ifs
  · exact Real.log_nonneg (one_le_cast.2 (Nat.minFac_pos n))
  rfl

中文:
定理 vonMangoldt_nonneg
  条件: {n : 自然数}
  结论: 0 <= Λ n
  证明: by
  rw [vonMangoldt_apply]
  split_ifs
  · exact Real.log_nonneg (one_le_cast.2 (Nat.minFac_pos n))
  rfl

Depends on / 依赖: Nat.minFac_pos, Real.log_nonneg, log_nonneg, minFac_pos, one_le_cast, split_ifs, vonMangoldt_apply
-/
theorem vonMangoldt_nonneg {n : Nat} : 0 <= Λ n := by
  rw [vonMangoldt_apply]
  split_ifs
  · exact Real.log_nonneg (one_le_cast.2 (Nat.minFac_pos n))
  rfl

/--
theorem `vonMangoldt_apply_pow` / 定理 `vonMangoldt_apply_pow`

English:
theorem vonMangoldt_apply_pow
  given: {n k : Nat} (hk : k != 0)
  statement: Λ (n ^ k) = Λ n
  proof: by
  simp only [vonMangoldt_apply, isPrimePow_pow_iff hk, pow_minFac hk]

中文:
定理 vonMangoldt_apply_pow
  条件: {n k : 自然数} (hk : k != 0)
  结论: Λ (n ^ k) = Λ n
  证明: by
  simp only [vonMangoldt_apply, isPrimePow_pow_iff hk, pow_minFac hk]

Depends on / 依赖: isPrimePow_pow_iff, pow_minFac, vonMangoldt_apply
-/
theorem vonMangoldt_apply_pow {n k : Nat} (hk : k != 0) : Λ (n ^ k) = Λ n := by
  simp only [vonMangoldt_apply, isPrimePow_pow_iff hk, pow_minFac hk]

/--
theorem `vonMangoldt_apply_prime` / 定理 `vonMangoldt_apply_prime`

English:
theorem vonMangoldt_apply_prime
  given: {p : Nat} (hp : p.Prime)
  statement: Λ p = Real.log p
  proof: by
  rw [vonMangoldt_apply]; rw [Prime.minFac_eq hp]; rw [if_pos hp.prime.isPrimePow]

中文:
定理 vonMangoldt_apply_prime
  条件: {p : 自然数} (hp : p.Prime)
  结论: Λ p = 实数.log p
  证明: by
  rw [vonMangoldt_apply]; rw [Prime.minFac_eq hp]; rw [if_pos hp.prime.isPrimePow]

Depends on / 依赖: Prime.minFac_eq, hp.prime.isPrimePow, if_pos, isPrimePow, minFac_eq, vonMangoldt_apply
-/
theorem vonMangoldt_apply_prime {p : Nat} (hp : p.Prime) : Λ p = Real.log p := by
  rw [vonMangoldt_apply]; rw [Prime.minFac_eq hp]; rw [if_pos hp.prime.isPrimePow]

/--
theorem `vonMangoldt_ne_zero_iff` / 定理 `vonMangoldt_ne_zero_iff`

English:
theorem vonMangoldt_ne_zero_iff
  given: {n : Nat}
  statement: Λ n != 0 ↔ IsPrimePow n
  proof: by
  rcases eq_or_ne n 1 with (rfl | hn); · simp [not_isPrimePow_one]
  exact (Real.log_pos (one_lt_cast.2 (minFac_prime hn).one_lt)).ne'.ite_ne_right_iff

中文:
定理 vonMangoldt_ne_zero_iff
  条件: {n : 自然数}
  结论: Λ n != 0 ↔ IsPrimePow n
  证明: by
  rcases eq_or_ne n 1 with (rfl | hn); · simp [not_isPrimePow_one]
  exact (Real.log_pos (one_lt_cast.2 (minFac_prime hn).one_lt)).ne'.ite_ne_right_iff

Depends on / 依赖: Real.log_pos, eq_or_ne, ite_ne_right_iff, log_pos, minFac_prime, not_isPrimePow_one, one_lt, one_lt_cast
-/
theorem vonMangoldt_ne_zero_iff {n : Nat} : Λ n != 0 ↔ IsPrimePow n := by
  rcases eq_or_ne n 1 with (rfl | hn); · simp [not_isPrimePow_one]
  exact (Real.log_pos (one_lt_cast.2 (minFac_prime hn).one_lt)).ne'.ite_ne_right_iff

/--
theorem `vonMangoldt_pos_iff` / 定理 `vonMangoldt_pos_iff`

English:
theorem vonMangoldt_pos_iff
  given: {n : Nat}
  statement: 0 < Λ n ↔ IsPrimePow n
  proof: vonMangoldt_nonneg.lt_iff_ne.trans (ne_comm.trans vonMangoldt_ne_zero_iff)

中文:
定理 vonMangoldt_pos_iff
  条件: {n : 自然数}
  结论: 0 < Λ n ↔ IsPrimePow n
  证明: vonMangoldt_nonneg.lt_iff_ne.trans (ne_comm.trans vonMangoldt_ne_zero_iff)

Depends on / 依赖: lt_iff_ne, ne_comm, ne_comm.trans, vonMangoldt_ne_zero_iff, vonMangoldt_nonneg, vonMangoldt_nonneg.lt_iff_ne.trans
-/
theorem vonMangoldt_pos_iff {n : Nat} : 0 < Λ n ↔ IsPrimePow n :=
  vonMangoldt_nonneg.lt_iff_ne.trans (ne_comm.trans vonMangoldt_ne_zero_iff)

/--
theorem `vonMangoldt_eq_zero_iff` / 定理 `vonMangoldt_eq_zero_iff`

English:
theorem vonMangoldt_eq_zero_iff
  given: {n : Nat}
  statement: Λ n = 0 ↔ ¬IsPrimePow n
  proof: vonMangoldt_ne_zero_iff.not_right

中文:
定理 vonMangoldt_eq_zero_iff
  条件: {n : 自然数}
  结论: Λ n = 0 ↔ ¬IsPrimePow n
  证明: vonMangoldt_ne_zero_iff.not_right

Depends on / 依赖: not_right, vonMangoldt_ne_zero_iff, vonMangoldt_ne_zero_iff.not_right
-/
theorem vonMangoldt_eq_zero_iff {n : Nat} : Λ n = 0 ↔ ¬IsPrimePow n :=
  vonMangoldt_ne_zero_iff.not_right

/--
theorem `vonMangoldt_sum` / 定理 `vonMangoldt_sum`

English:
theorem vonMangoldt_sum
  given: {n : Nat}
  statement: ∑ i in n.divisors, Λ i = Real.log n
  proof: by
  refine recOnPrimeCoprime ?_ ?_ ?_ n
  · simp
  · intro p k hp
    rw [sum_divisors_prime_pow hp]; rw [cast_pow]; rw [Real.log_pow]; rw [Finset.sum_range_succ']; rw [Nat.pow_zero]; rw [vonMangoldt_apply_one]
    simp [vonMangoldt_apply_pow (Nat.succ_ne_zero _), vonMangoldt_apply_prime hp]
  intr

中文:
定理 vonMangoldt_sum
  条件: {n : 自然数}
  结论: ∑ i in n.divisors, Λ i = 实数.log n
  证明: by
  refine recOnPrimeCoprime ?_ ?_ ?_ n
  · simp
  · intro p k hp
    rw [sum_divisors_prime_pow hp]; rw [cast_pow]; rw [Real.log_pow]; rw [Finset.sum_range_succ']; rw [Nat.pow_zero]; rw [vonMangoldt_apply_one]
    simp [vonMangoldt_apply_pow (Nat.succ_ne_zero _), vonMangoldt_apply_prime hp]
  intr

Depends on / 依赖: Finset, Finset.sum_range_succ, Nat.pow_zero, Nat.succ_ne_zero, Real.log_pow, cast_pow, disjoint_divisors_filter_isPrimePow, filter_union, log_pow, mul_divisors_filter_prime_pow, pow_zero, recOnPrimeCoprime, succ_ne_zero, sum_divisors_prime_pow, sum_filter, sum_range_succ, sum_union, vonMangoldt_apply, vonMangoldt_apply_one, vonMangoldt_apply_pow
-/
theorem vonMangoldt_sum {n : Nat} : ∑ i in n.divisors, Λ i = Real.log n := by
  refine recOnPrimeCoprime ?_ ?_ ?_ n
  · simp
  · intro p k hp
    rw [sum_divisors_prime_pow hp]; rw [cast_pow]; rw [Real.log_pow]; rw [Finset.sum_range_succ']; rw [Nat.pow_zero]; rw [vonMangoldt_apply_one]
    simp [vonMangoldt_apply_pow (Nat.succ_ne_zero _), vonMangoldt_apply_prime hp]
  intro a b ha' hb' hab ha hb
  simp only [vonMangoldt_apply, ← sum_filter] at ha hb ⊢
  rw [mul_divisors_filter_prime_pow hab]; rw [filter_union]; rw [sum_union (disjoint_divisors_filter_isPrimePow hab)]; rw [ha]; rw [hb]; rw [Nat.cast_mul]; rw [Real.log_mul (cast_ne_zero.2 (pos_of_gt ha').ne') (cast_ne_zero.2 (pos_of_gt hb').ne')]

-- access notation `ζ` and `μ`
open scoped zeta Moebius

@[simp]
/--
theorem `vonMangoldt_mul_zeta` / 定理 `vonMangoldt_mul_zeta`

English:
theorem vonMangoldt_mul_zeta
  statement: Λ * ζ = log
  proof: by
  ext n; rw [coe_mul_zeta_apply, vonMangoldt_sum]; rfl

@[simp]

中文:
定理 vonMangoldt_mul_zeta
  结论: Λ * ζ = log
  证明: by
  ext n; rw [coe_mul_zeta_apply, vonMangoldt_sum]; rfl

@[simp]

Depends on / 依赖: coe_mul_zeta_apply, vonMangoldt_sum
-/
theorem vonMangoldt_mul_zeta : Λ * ζ = log := by
  ext n; rw [coe_mul_zeta_apply, vonMangoldt_sum]; rfl

@[simp]
/--
theorem `zeta_mul_vonMangoldt` / 定理 `zeta_mul_vonMangoldt`

English:
theorem zeta_mul_vonMangoldt
  statement: (ζ : ArithmeticFunction Real) * Λ = log
  proof: by rw [mul_comm]; simp

@[simp]

中文:
定理 zeta_mul_vonMangoldt
  结论: (ζ : ArithmeticFunction 实数) * Λ = log
  证明: by rw [mul_comm]; simp

@[simp]

Depends on / 依赖: mul_comm
-/
theorem zeta_mul_vonMangoldt : (ζ : ArithmeticFunction Real) * Λ = log := by rw [mul_comm]; simp

@[simp]
/--
theorem `log_mul_moebius_eq_vonMangoldt` / 定理 `log_mul_moebius_eq_vonMangoldt`

English:
theorem log_mul_moebius_eq_vonMangoldt
  statement: log * μ = Λ
  proof: by
  rw [← vonMangoldt_mul_zeta]; rw [mul_assoc]; rw [coe_zeta_mul_coe_moebius]; rw [mul_one]

@[simp]

中文:
定理 log_mul_moebius_eq_vonMangoldt
  结论: log * μ = Λ
  证明: by
  rw [← vonMangoldt_mul_zeta]; rw [mul_assoc]; rw [coe_zeta_mul_coe_moebius]; rw [mul_one]

@[simp]

Depends on / 依赖: coe_zeta_mul_coe_moebius, mul_assoc, mul_one, vonMangoldt_mul_zeta
-/
theorem log_mul_moebius_eq_vonMangoldt : log * μ = Λ := by
  rw [← vonMangoldt_mul_zeta]; rw [mul_assoc]; rw [coe_zeta_mul_coe_moebius]; rw [mul_one]

@[simp]
/--
theorem `moebius_mul_log_eq_vonMangoldt` / 定理 `moebius_mul_log_eq_vonMangoldt`

English:
theorem moebius_mul_log_eq_vonMangoldt
  statement: (μ : ArithmeticFunction Real) * log = Λ
  proof: by
  rw [mul_comm]; simp

中文:
定理 moebius_mul_log_eq_vonMangoldt
  结论: (μ : ArithmeticFunction 实数) * log = Λ
  证明: by
  rw [mul_comm]; simp

Depends on / 依赖: mul_comm
-/
theorem moebius_mul_log_eq_vonMangoldt : (μ : ArithmeticFunction Real) * log = Λ := by
  rw [mul_comm]; simp

/--
theorem `sum_moebius_mul_log_eq` / 定理 `sum_moebius_mul_log_eq`

English:
theorem sum_moebius_mul_log_eq
  given: {n : Nat}
  statement: (∑ d in n.divisors, (μ d : Real) * log d) = -Λ n
  proof: by
  simp only [← log_mul_moebius_eq_vonMangoldt, mul_comm log, mul_apply, log_apply, intCoe_apply, ←
    Finset.sum_neg_distrib, neg_mul_eq_mul_neg]
  rw [sum_divisorsAntidiagonal fun i j => (μ i : Real) * -Real.log j]
  have : (∑ i in n.divisors, (μ i : Real) * -Real.log (n / i : Nat)) =
      ∑ i

中文:
定理 sum_moebius_mul_log_eq
  条件: {n : 自然数}
  结论: (∑ d in n.divisors, (μ d : 实数) * log d) = -Λ n
  证明: by
  simp only [← log_mul_moebius_eq_vonMangoldt, mul_comm log, mul_apply, log_apply, intCoe_apply, ←
    Finset.sum_neg_distrib, neg_mul_eq_mul_neg]
  rw [sum_divisorsAntidiagonal fun i j => (μ i : Real) * -Real.log j]
  have : (∑ i in n.divisors, (μ i : Real) * -Real.log (n / i : Nat)) =
      ∑ i

Depends on / 依赖: Finset, Finset.sum_neg_distrib, Real.log, and_imp, cast_ne_zero, divisors, intCoe_apply, log_apply, log_mul_moebius_eq_vonMangoldt, mem_divisors, mul_apply, mul_comm, n.divisors, neg_mul_eq_mul_neg, sum_congr, sum_divisorsAntidiagonal, sum_neg_distrib
-/
theorem sum_moebius_mul_log_eq {n : Nat} : (∑ d in n.divisors, (μ d : Real) * log d) = -Λ n := by
  simp only [← log_mul_moebius_eq_vonMangoldt, mul_comm log, mul_apply, log_apply, intCoe_apply, ←
    Finset.sum_neg_distrib, neg_mul_eq_mul_neg]
  rw [sum_divisorsAntidiagonal fun i j => (μ i : Real) * -Real.log j]
  have : (∑ i in n.divisors, (μ i : Real) * -Real.log (n / i : Nat)) =
      ∑ i in n.divisors, ((μ i : Real) * Real.log i - μ i * Real.log n) := by
    apply sum_congr rfl
    simp only [and_imp, Ne, mem_divisors]
    intro m mn hn
    have : (m : Real) != 0 := by
      rw [cast_ne_zero]
      rintro rfl
      exact hn (by simpa using mn)
    rw [Nat.cast_div mn this]; rw [Real.log_div (cast_ne_zero.2 hn) this]; rw [neg_sub]; rw [mul_sub]
  rw [this]; rw [sum_sub_distrib]; rw [← sum_mul]; rw [← Int.cast_sum]; rw [← coe_mul_zeta_apply]; rw [eq_comm]; rw [sub_eq_self]; rw [moebius_mul_coe_zeta]
  rcases eq_or_ne n 1 with (hn | hn) <;> simp [hn]

/--
theorem `vonMangoldt_le_log` / 定理 `vonMangoldt_le_log`

English:
theorem vonMangoldt_le_log
  statement: forall {n : Nat}, Λ n <= Real.log (n : Real)

中文:
定理 vonMangoldt_le_log
  结论: 对任意 {n : 自然数}, Λ n <= 实数.log (n : 实数)
-/
theorem vonMangoldt_le_log : forall {n : Nat}, Λ n <= Real.log (n : Real)
  | 0 => by simp
  | n + 1 => by
    rw [← vonMangoldt_sum]
    exact single_le_sum (by exact fun _ _ => vonMangoldt_nonneg)
      (mem_divisors_self _ n.succ_ne_zero)

end ArithmeticFunction

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: the von Mangoldt function is nonnegative. -/
@[positivity ArithmeticFunction.vonMangoldt _]
meta def evalVonMangoldt : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(@ArithmeticFunction.vonMangoldt $a) =>
    assertInstancesCommute
    pure (.nonnegative q(ArithmeticFunction.vonMangoldt_nonneg))
  | _, _, _ => throwError "not von Mangoldt"

end Mathlib.Meta.Positivity
