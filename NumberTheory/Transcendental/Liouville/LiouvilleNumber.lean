/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Jujian Zhang
-/
module

public import Mathlib.NumberTheory.Transcendental.Liouville.Basic

/-!

# Liouville constants

This file contains a construction of a family of Liouville numbers, indexed by a natural number $m$.
The most important property is that they are examples of transcendental real numbers.
This fact is recorded in `transcendental_liouvilleNumber`.

More precisely, for a real number $m$, Liouville's constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}.
$$
The series converges only for $1 < m$. However, there is no restriction on $m$, since,
if the series does not converge, then the sum of the series is defined to be zero.

We prove that, for $m \in \mathbb{N}$ satisfying $2 \le m$, Liouville's constant associated to $m$
is a transcendental number. Classically, the Liouville number for $m = 2$ is the one called
"Liouville's constant".

## Implementation notes

The indexing $m$ is eventually a natural number satisfying $2 ≤ m$. However, we prove the first few
lemmas for $m \in \mathbb{R}$.
-/

@[expose] public section


noncomputable section

open scoped Nat

open Real Finset

/--
Definition of `liouvilleNumber` / `liouvilleNumber` 的定义

English:
definition liouvilleNumber
  signature: (m : Real)
  body: ∑' i : Nat, 1 / m ^ i !

中文:
定义 liouvilleNumber
  签名: (m : 实数)
  定义体: ∑' i : Nat, 1 / m ^ i !
-/
def liouvilleNumber (m : Real) : Real :=
  ∑' i : Nat, 1 / m ^ i !

namespace LiouvilleNumber

/--
Definition of `partialSum` / `partialSum` 的定义

English:
definition partialSum
  signature: (m : Real) (k : Nat)
  body: ∑ i in range (k + 1), 1 / m ^ i !

中文:
定义 partialSum
  签名: (m : 实数) (k : 自然数)
  定义体: ∑ i in range (k + 1), 1 / m ^ i !
-/
def partialSum (m : Real) (k : Nat) : Real :=
  ∑ i in range (k + 1), 1 / m ^ i !

/--
Definition of `remainder` / `remainder` 的定义

English:
definition remainder
  signature: (m : Real) (k : Nat)
  body: ∑' i, 1 / m ^ (i + (k + 1))!

中文:
定义 remainder
  签名: (m : 实数) (k : 自然数)
  定义体: ∑' i, 1 / m ^ (i + (k + 1))!
-/
def remainder (m : Real) (k : Nat) : Real :=
  ∑' i, 1 / m ^ (i + (k + 1))!



/--
theorem `summable` / 定理 `summable`

English:
theorem summable
  given: {m : Real} (hm : 1 < m)
  statement: Summable fun i : Nat => 1 / m ^ i !
  proof: summable_one_div_pow_of_le hm Nat.self_le_factorial

中文:
定理 summable
  条件: {m : 实数} (hm : 1 < m)
  结论: Summable fun i : 自然数 => 1 / m ^ i !
  证明: summable_one_div_pow_of_le hm Nat.self_le_factorial
-/
protected theorem summable {m : Real} (hm : 1 < m) : Summable fun i : Nat => 1 / m ^ i ! :=
  summable_one_div_pow_of_le hm Nat.self_le_factorial

/--
theorem `remainder_summable` / 定理 `remainder_summable`

English:
theorem remainder_summable
  given: {m : Real} (hm : 1 < m) (k : Nat)
  proof: by
  convert! (summable_nat_add_iff (k + 1)).2 (LiouvilleNumber.summable hm)

中文:
定理 remainder_summable
  条件: {m : 实数} (hm : 1 < m) (k : 自然数)
  证明: by
  convert! (summable_nat_add_iff (k + 1)).2 (LiouvilleNumber.summable hm)

Depends on / 依赖: LiouvilleNumber, LiouvilleNumber.summable, convert, summable, summable_nat_add_iff
-/
theorem remainder_summable {m : Real} (hm : 1 < m) (k : Nat) :
    Summable fun i : Nat => 1 / m ^ (i + (k + 1))! := by
  convert! (summable_nat_add_iff (k + 1)).2 (LiouvilleNumber.summable hm)

/--
theorem `remainder_pos` / 定理 `remainder_pos`

English:
theorem remainder_pos
  given: {m : Real} (hm : 1 < m) (k : Nat)
  statement: 0 < remainder m k
  proof: (remainder_summable hm k).tsum_pos (fun _ => by positivity) 0 (by positivity)

中文:
定理 remainder_pos
  条件: {m : 实数} (hm : 1 < m) (k : 自然数)
  结论: 0 < remainder m k
  证明: (remainder_summable hm k).tsum_pos (fun _ => by positivity) 0 (by positivity)

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, IsSFiniteKernel, IsSFiniteKernel.withDensity, coe_ne_top, remainder_summable, tsum_pos, withDensity
-/
theorem remainder_pos {m : Real} (hm : 1 < m) (k : Nat) : 0 < remainder m k :=
  (remainder_summable hm k).tsum_pos (fun _ => by positivity) 0 (by positivity)

/--
theorem `partialSum_succ` / 定理 `partialSum_succ`

English:
theorem partialSum_succ
  given: (m : Real) (n : Nat)
  proof: sum_range_succ _ _

中文:
定理 partialSum_succ
  条件: (m : 实数) (n : 自然数)
  证明: sum_range_succ _ _

Depends on / 依赖: sum_range_succ
-/
theorem partialSum_succ (m : Real) (n : Nat) :
    partialSum m (n + 1) = partialSum m n + 1 / m ^ (n + 1)! :=
  sum_range_succ _ _

/--
theorem `partialSum_add_remainder` / 定理 `partialSum_add_remainder`

English:
theorem partialSum_add_remainder
  given: {m : Real} (hm : 1 < m) (k : Nat)
  proof: (LiouvilleNumber.summable hm).sum_add_tsum_nat_add _

中文:
定理 partialSum_add_remainder
  条件: {m : 实数} (hm : 1 < m) (k : 自然数)
  证明: (LiouvilleNumber.summable hm).sum_add_tsum_nat_add _

Depends on / 依赖: LiouvilleNumber, LiouvilleNumber.summable, property, sum_add_tsum_nat_add, summable
-/
theorem partialSum_add_remainder {m : Real} (hm : 1 < m) (k : Nat) :
    partialSum m k + remainder m k = liouvilleNumber m :=
  (LiouvilleNumber.summable hm).sum_add_tsum_nat_add _

/-! We now prove two useful inequalities, before collecting everything together. -/


/--
theorem `remainder_lt'` / 定理 `remainder_lt'`

English:
theorem remainder_lt'
  given: (n : Nat) {m : Real} (m1 : 1 < m)
  proof: -- two useful inequalities
  have m0 : 0 < m := zero_lt_one.trans m1
  have mi : 1 / m < 1 := (div_lt_one m0).mpr m1
  -- to show the strict inequality between these series, we prove that:
  calc
    (∑' i, 1 / m ^ (i + (n + 1))!) < ∑' i, 1 / m ^ (i + (n + 1)!) :=
        -- 1. the second series dominates the first
        Summable.tsum_lt_tsum (fun b => one_div_pow_le_one_div_pow_of_le m1.le
          (b.add_factorial_succ_le_factorial_add_succ n))
        -- 2. the term with index `i = 2` of the first series is strictly smaller than
        -- the corresponding term of the second series
        (one_div_pow_strictAnti m1 (n.add_factorial_succ_lt_factorial_add_succ (i := 2) le_rfl))
        -- 3. the first series is summable
        (remainder_summable m1 n)
        -- 4. the second series is summable, since its terms grow quickly
        (summable_one_div_pow_of_le m1 fun _ => le_self_add)
    -- split the sum in the exponent and massage
    _ = ∑' i : Nat, (1 / m) ^ i * (1 / m ^ (n + 1)!) := by
      simp only [pow_add, one_div, mul_inv, inv_pow]
    -- factor the constant `(1 / m ^ (n + 1)!)` out of the series
    _ = (∑' i, (1 / m) ^ i) * (1 / m ^ (n + 1)!) := tsum_mul_right
    -- the series is the geometric series
    _ = (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) := by rw [tsum_geometric_of_lt_one (by positivity) mi]

中文:
定理 remainder_lt'
  条件: (n : 自然数) {m : 实数} (m1 : 1 < m)
  证明: -- two useful inequalities
  have m0 : 0 < m := zero_lt_one.trans m1
  have mi : 1 / m < 1 := (div_lt_one m0).mpr m1
  -- to show the strict inequality between these series, we prove that:
  calc
    (∑' i, 1 / m ^ (i + (n + 1))!) < ∑' i, 1 / m ^ (i + (n + 1)!) :=
        -- 1. the second series dominates the first
        Summable.tsum_lt_tsum (fun b => one_div_pow_le_one_div_pow_of_le m1.le
          (b.add_factorial_succ_le_factorial_add_succ n))
        -- 2. the term with index `i = 2` of the first series is strictly smaller than
        -- the corresponding term of the second series
        (one_div_pow_strictAnti m1 (n.add_factorial_succ_lt_factorial_add_succ (i := 2) le_rfl))
        -- 3. the first series is summable
        (remainder_summable m1 n)
        -- 4. the second series is summable, since its terms grow quickly
        (summable_one_div_pow_of_le m1 fun _ => le_self_add)
    -- split the sum in the exponent and massage
    _ = ∑' i : Nat, (1 / m) ^ i * (1 / m ^ (n + 1)!) := by
      simp only [pow_add, one_div, mul_inv, inv_pow]
    -- factor the constant `(1 / m ^ (n + 1)!)` out of the series
    _ = (∑' i, (1 / m) ^ i) * (1 / m ^ (n + 1)!) := tsum_mul_right
    -- the series is the geometric series
    _ = (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) := by rw [tsum_geometric_of_lt_one (by positivity) mi]
-/
theorem remainder_lt' (n : Nat) {m : Real} (m1 : 1 < m) :
    remainder m n < (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) :=
  -- two useful inequalities
  have m0 : 0 < m := zero_lt_one.trans m1
  have mi : 1 / m < 1 := (div_lt_one m0).mpr m1
  -- to show the strict inequality between these series, we prove that:
  calc
    (∑' i, 1 / m ^ (i + (n + 1))!) < ∑' i, 1 / m ^ (i + (n + 1)!) :=
        -- 1. the second series dominates the first
        Summable.tsum_lt_tsum (fun b => one_div_pow_le_one_div_pow_of_le m1.le
          (b.add_factorial_succ_le_factorial_add_succ n))
        -- 2. the term with index `i = 2` of the first series is strictly smaller than
        -- the corresponding term of the second series
        (one_div_pow_strictAnti m1 (n.add_factorial_succ_lt_factorial_add_succ (i := 2) le_rfl))
        -- 3. the first series is summable
        (remainder_summable m1 n)
        -- 4. the second series is summable, since its terms grow quickly
        (summable_one_div_pow_of_le m1 fun _ => le_self_add)
    -- split the sum in the exponent and massage
    _ = ∑' i : Nat, (1 / m) ^ i * (1 / m ^ (n + 1)!) := by
      simp only [pow_add, one_div, mul_inv, inv_pow]
    -- factor the constant `(1 / m ^ (n + 1)!)` out of the series
    _ = (∑' i, (1 / m) ^ i) * (1 / m ^ (n + 1)!) := tsum_mul_right
    -- the series is the geometric series
    _ = (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) := by rw [tsum_geometric_of_lt_one (by positivity) mi]

/--
theorem `aux_calc` / 定理 `aux_calc`

English:
theorem aux_calc
  given: (n : Nat) {m : Real} (hm : 2 <= m)
  proof: calc
    (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) <= 2 * (1 / m ^ (n + 1)!) := by
      -- the second factors coincide (and are non-negative),
      -- the first factors satisfy the inequality `sub_one_div_inv_le_two`
      gcongr; exact sub_one_div_inv_le_two hm
    _ = 2 / m ^ (n + 1)! := mul_one_div 2 _
    _ = 2 / m ^ (n ! * (n + 1)) := (congr_arg (2 / ·) (congr_arg (Pow.pow m) (mul_comm _ _)))
    _ <= 1 / (m ^ n !) ^ n := by
      -- Clear denominators and massage*
      rw [← pow_mul]; rw [div_le_div_iff₀]; rw [one_mul]; rw [mul_add_one]; rw [pow_add]; rw [mul_comm 2]
      · gcongr
        -- `2 ≤ m ^ n!` is a consequence of monotonicity of exponentiation at `2 ≤ m`.
exact hm.trans le_self_pow₀ (one_le_two.trans hm) by positivity
      all_goals positivity

中文:
定理 aux_calc
  条件: (n : 自然数) {m : 实数} (hm : 2 <= m)
  证明: calc
    (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) <= 2 * (1 / m ^ (n + 1)!) := by
      -- the second factors coincide (and are non-negative),
      -- the first factors satisfy the inequality `sub_one_div_inv_le_two`
      gcongr; exact sub_one_div_inv_le_two hm
    _ = 2 / m ^ (n + 1)! := mul_one_div 2 _
    _ = 2 / m ^ (n ! * (n + 1)) := (congr_arg (2 / ·) (congr_arg (Pow.pow m) (mul_comm _ _)))
    _ <= 1 / (m ^ n !) ^ n := by
      -- Clear denominators and massage*
      rw [← pow_mul]; rw [div_le_div_iff₀]; rw [one_mul]; rw [mul_add_one]; rw [pow_add]; rw [mul_comm 2]
      · gcongr
        -- `2 ≤ m ^ n!` is a consequence of monotonicity of exponentiation at `2 ≤ m`.
exact hm.trans le_self_pow₀ (one_le_two.trans hm) by positivity
      all_goals positivity
-/
theorem aux_calc (n : Nat) {m : Real} (hm : 2 <= m) :
    (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) <= 1 / (m ^ n !) ^ n :=
  calc
    (1 - 1 / m)⁻¹ * (1 / m ^ (n + 1)!) <= 2 * (1 / m ^ (n + 1)!) := by
      -- the second factors coincide (and are non-negative),
      -- the first factors satisfy the inequality `sub_one_div_inv_le_two`
      gcongr; exact sub_one_div_inv_le_two hm
    _ = 2 / m ^ (n + 1)! := mul_one_div 2 _
    _ = 2 / m ^ (n ! * (n + 1)) := (congr_arg (2 / ·) (congr_arg (Pow.pow m) (mul_comm _ _)))
    _ <= 1 / (m ^ n !) ^ n := by
      -- Clear denominators and massage*
      rw [← pow_mul]; rw [div_le_div_iff₀]; rw [one_mul]; rw [mul_add_one]; rw [pow_add]; rw [mul_comm 2]
      · gcongr
        -- `2 ≤ m ^ n!` is a consequence of monotonicity of exponentiation at `2 ≤ m`.
exact hm.trans le_self_pow₀ (one_le_two.trans hm) by positivity
      all_goals positivity

/--
theorem `remainder_lt` / 定理 `remainder_lt`

English:
theorem remainder_lt
  given: (n : Nat) {m : Real} (m2 : 2 <= m)
  statement: remainder m n < 1 / (m ^ n !) ^ n
  proof: (remainder_lt' n <| one_lt_two.trans_le m2).trans_le (aux_calc _ m2)

中文:
定理 remainder_lt
  条件: (n : 自然数) {m : 实数} (m2 : 2 <= m)
  结论: remainder m n < 1 / (m ^ n !) ^ n
  证明: (remainder_lt' n <| one_lt_two.trans_le m2).trans_le (aux_calc _ m2)

Depends on / 依赖: aux_calc, one_lt_two, one_lt_two.trans_le, remainder_lt, trans_le
-/
theorem remainder_lt (n : Nat) {m : Real} (m2 : 2 <= m) : remainder m n < 1 / (m ^ n !) ^ n :=
  (remainder_lt' n <| one_lt_two.trans_le m2).trans_le (aux_calc _ m2)

/-! Starting from here, we specialize to the case in which `m` is a natural number. -/


/--
theorem `partialSum_eq_rat` / 定理 `partialSum_eq_rat`

English:
theorem partialSum_eq_rat
  given: {m : Nat} (hm : 0 < m) (k : Nat)
  proof: by
  induction k with
  | zero => exact ⟨1, by rw [partialSum, range_one, sum_singleton, Nat.cast_one, Nat.factorial,
      pow_one, pow_one]⟩
  | succ k h =>
    rcases h with ⟨p_k, h_k⟩
    use p_k * m ^ ((k + 1)! - k !) + 1
    rw [partialSum_succ]; rw [h_k]; rw [div_add_div]; rw [div_eq_div_iff]; rw [add_mul]
    · norm_cast
      rw [add_mul]; rw [one_mul]; rw [Nat.factorial_succ]; rw [add_mul]; rw [one_mul]; rw [add_tsub_cancel_right]; rw [pow_add]
      simp [mul_assoc]
    all_goals positivity

中文:
定理 partialSum_eq_rat
  条件: {m : 自然数} (hm : 0 < m) (k : 自然数)
  证明: by
  induction k with
  | zero => exact ⟨1, by rw [partialSum, range_one, sum_singleton, Nat.cast_one, Nat.factorial,
      pow_one, pow_one]⟩
  | succ k h =>
    rcases h with ⟨p_k, h_k⟩
    use p_k * m ^ ((k + 1)! - k !) + 1
    rw [partialSum_succ]; rw [h_k]; rw [div_add_div]; rw [div_eq_div_iff]; rw [add_mul]
    · norm_cast
      rw [add_mul]; rw [one_mul]; rw [Nat.factorial_succ]; rw [add_mul]; rw [one_mul]; rw [add_tsub_cancel_right]; rw [pow_add]
      simp [mul_assoc]
    all_goals positivity

Depends on / 依赖: Nat.cast_one, Nat.factorial, Nat.factorial_succ, add_mul, add_tsub_cancel_right, all_goals, cast_one, div_add_div, div_eq_div_iff, factorial, factorial_succ, mul_assoc, one_mul, partialSum, partialSum_succ, pow_add, pow_one, range_one, sum_singleton
-/
theorem partialSum_eq_rat {m : Nat} (hm : 0 < m) (k : Nat) :
    exists p : Nat, partialSum m k = p / ((m ^ k ! :) : Real) := by
  induction k with
  | zero => exact ⟨1, by rw [partialSum, range_one, sum_singleton, Nat.cast_one, Nat.factorial,
      pow_one, pow_one]⟩
  | succ k h =>
    rcases h with ⟨p_k, h_k⟩
    use p_k * m ^ ((k + 1)! - k !) + 1
    rw [partialSum_succ]; rw [h_k]; rw [div_add_div]; rw [div_eq_div_iff]; rw [add_mul]
    · norm_cast
      rw [add_mul]; rw [one_mul]; rw [Nat.factorial_succ]; rw [add_mul]; rw [one_mul]; rw [add_tsub_cancel_right]; rw [pow_add]
      simp [mul_assoc]
    all_goals positivity

end LiouvilleNumber

open LiouvilleNumber

/--
theorem `liouville_liouvilleNumber` / 定理 `liouville_liouvilleNumber`

English:
theorem liouville_liouvilleNumber
  given: {m : Nat} (hm : 2 <= m)
  statement: Liouville (liouvilleNumber m)
  proof: by
  -- two useful inequalities
  have mZ1 : 1 < (m : Int) := by norm_cast
  have m1 : 1 < (m : Real) := by norm_cast
  intro n
  -- the first `n` terms sum to `p / m ^ k!`
  rcases partialSum_eq_rat (zero_lt_two.trans_le hm) n with ⟨p, hp⟩
  refine ⟨p, m ^ n !, one_lt_pow₀ mZ1 n.factorial_ne_zero, ?_⟩
  push_cast
  rw [Nat.cast_pow] at hp
  -- separate out the sum of the first `n` terms and the rest
  rw [← partialSum_add_remainder m1 n]; rw [← hp]
  have hpos := remainder_pos m1 n
  simpa [abs_of_pos hpos, hpos.ne'] using @remainder_lt n m (by assumption_mod_cast)

中文:
定理 liouville_liouvilleNumber
  条件: {m : 自然数} (hm : 2 <= m)
  结论: Liouville (liouvilleNumber m)
  证明: by
  -- two useful inequalities
  have mZ1 : 1 < (m : Int) := by norm_cast
  have m1 : 1 < (m : Real) := by norm_cast
  intro n
  -- the first `n` terms sum to `p / m ^ k!`
  rcases partialSum_eq_rat (zero_lt_two.trans_le hm) n with ⟨p, hp⟩
  refine ⟨p, m ^ n !, one_lt_pow₀ mZ1 n.factorial_ne_zero, ?_⟩
  push_cast
  rw [Nat.cast_pow] at hp
  -- separate out the sum of the first `n` terms and the rest
  rw [← partialSum_add_remainder m1 n]; rw [← hp]
  have hpos := remainder_pos m1 n
  simpa [abs_of_pos hpos, hpos.ne'] using @remainder_lt n m (by assumption_mod_cast)

Depends on / 依赖: Kernel, Kernel.discard, discard, infer_instance
-/
theorem liouville_liouvilleNumber {m : Nat} (hm : 2 <= m) : Liouville (liouvilleNumber m) := by
  -- two useful inequalities
  have mZ1 : 1 < (m : Int) := by norm_cast
  have m1 : 1 < (m : Real) := by norm_cast
  intro n
  -- the first `n` terms sum to `p / m ^ k!`
  rcases partialSum_eq_rat (zero_lt_two.trans_le hm) n with ⟨p, hp⟩
  refine ⟨p, m ^ n !, one_lt_pow₀ mZ1 n.factorial_ne_zero, ?_⟩
  push_cast
  rw [Nat.cast_pow] at hp
  -- separate out the sum of the first `n` terms and the rest
  rw [← partialSum_add_remainder m1 n]; rw [← hp]
  have hpos := remainder_pos m1 n
  simpa [abs_of_pos hpos, hpos.ne'] using @remainder_lt n m (by assumption_mod_cast)

/--
theorem `transcendental_liouvilleNumber` / 定理 `transcendental_liouvilleNumber`

English:
theorem transcendental_liouvilleNumber
  given: {m : Nat} (hm : 2 <= m)
  proof: (liouville_liouvilleNumber hm).transcendental

中文:
定理 transcendental_liouvilleNumber
  条件: {m : 自然数} (hm : 2 <= m)
  证明: (liouville_liouvilleNumber hm).transcendental

Depends on / 依赖: liouville_liouvilleNumber, transcendental
-/
theorem transcendental_liouvilleNumber {m : Nat} (hm : 2 <= m) :
    Transcendental Int (liouvilleNumber m) :=
  (liouville_liouvilleNumber hm).transcendental
