/-
Copyright (c) 2022 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Fabian Kruse, Nikolas Kuhn
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Wallis
public import Mathlib.Tactic.AdaptationNote

/-!
# Stirling's formula

This file proves Stirling's formula for the factorial.
It states that $n!$ grows asymptotically like $\sqrt{2\pi n}(\frac{n}{e})^n$.

Also some _global_ bounds on the factorial function and the Stirling sequence are proved.

## Proof outline

The proof follows: <https://proofwiki.org/wiki/Stirling%27s_Formula>.

We proceed in two parts.

**Part 1**: We consider the sequence $a_n$ of fractions $\frac{n!}{\sqrt{2n}(\frac{n}{e})^n}$
and prove that this sequence converges to a real, positive number $a$. For this the two main
ingredients are
- taking the logarithm of the sequence and
- using the series expansion of $\log(1 + x)$.

**Part 2**: We use the fact that the series defined in part 1 converges against a real number $a$
and prove that $a = \sqrt{\pi}$. Here the main ingredient is the convergence of Wallis' product
formula for `π`.
-/

@[expose] public section


open scoped Topology Real Nat Asymptotics

open Nat hiding log log_pow
open Finset Filter Real

namespace Stirling

/-!
### Part 1
https://proofwiki.org/wiki/Stirling%27s_Formula#Part_1
-/


/--
Definition of `stirlingSeq` / `stirlingSeq` 的定义

English:
definition stirlingSeq
  signature: (n : Nat)
  body: n ! / (√(2 * n : Real) * (n / exp 1) ^ n)

@[simp]

中文:
定义 stirlingSeq
  签名: (n : 自然数)
  定义体: n ! / (√(2 * n : Real) * (n / exp 1) ^ n)

@[simp]
-/
noncomputable def stirlingSeq (n : Nat) : Real :=
  n ! / (√(2 * n : Real) * (n / exp 1) ^ n)

@[simp]
/--
theorem `stirlingSeq_zero` / 定理 `stirlingSeq_zero`

English:
theorem stirlingSeq_zero
  statement: stirlingSeq 0 = 0
  proof: by
  rw [stirlingSeq]; rw [cast_zero]; rw [mul_zero]; rw [Real.sqrt_zero]; rw [zero_mul]; rw [div_zero]

@[simp]

中文:
定理 stirlingSeq_zero
  结论: stirlingSeq 0 = 0
  证明: by
  rw [stirlingSeq]; rw [cast_zero]; rw [mul_zero]; rw [Real.sqrt_zero]; rw [zero_mul]; rw [div_zero]

@[simp]

Depends on / 依赖: Real.sqrt_zero, cast_zero, div_zero, mul_zero, sqrt_zero, stirlingSeq, zero_mul
-/
theorem stirlingSeq_zero : stirlingSeq 0 = 0 := by
  rw [stirlingSeq]; rw [cast_zero]; rw [mul_zero]; rw [Real.sqrt_zero]; rw [zero_mul]; rw [div_zero]

@[simp]
/--
theorem `stirlingSeq_one` / 定理 `stirlingSeq_one`

English:
theorem stirlingSeq_one
  statement: stirlingSeq 1 = exp 1 / √2
  proof: by
  rw [stirlingSeq]; rw [pow_one]; rw [factorial_one]; rw [cast_one]; rw [mul_one]; rw [mul_one_div]; rw [one_div_div]

中文:
定理 stirlingSeq_one
  结论: stirlingSeq 1 = exp 1 / √2
  证明: by
  rw [stirlingSeq]; rw [pow_one]; rw [factorial_one]; rw [cast_one]; rw [mul_one]; rw [mul_one_div]; rw [one_div_div]

Depends on / 依赖: cast_one, factorial_one, mul_one, mul_one_div, one_div_div, pow_one, stirlingSeq
-/
theorem stirlingSeq_one : stirlingSeq 1 = exp 1 / √2 := by
  rw [stirlingSeq]; rw [pow_one]; rw [factorial_one]; rw [cast_one]; rw [mul_one]; rw [mul_one_div]; rw [one_div_div]

/--
theorem `log_stirlingSeq_formula` / 定理 `log_stirlingSeq_formula`

English:
theorem log_stirlingSeq_formula
  given: (n : Nat)
  proof: by
  cases n
  · simp
  · rw [stirlingSeq, log_div, log_mul, sqrt_eq_rpow, log_rpow, Real.log_pow, tsub_tsub]
      <;> positivity

中文:
定理 log_stirlingSeq_formula
  条件: (n : 自然数)
  证明: by
  cases n
  · simp
  · rw [stirlingSeq, log_div, log_mul, sqrt_eq_rpow, log_rpow, Real.log_pow, tsub_tsub]
      <;> positivity

Depends on / 依赖: Real.log_pow, log_div, log_mul, log_pow, log_rpow, sqrt_eq_rpow, stirlingSeq, tsub_tsub, z.app
-/
theorem log_stirlingSeq_formula (n : Nat) :
    log (stirlingSeq n) = Real.log n ! - 1 / 2 * Real.log (2 * n) - n * log (n / exp 1) := by
  cases n
  · simp
  · rw [stirlingSeq, log_div, log_mul, sqrt_eq_rpow, log_rpow, Real.log_pow, tsub_tsub]
      <;> positivity

/--
theorem `log_stirlingSeq_sdiff_hasSum` / 定理 `log_stirlingSeq_sdiff_hasSum`

English:
theorem log_stirlingSeq_sdiff_hasSum
  given: (m : Nat)
  proof: by
  let f (k : Nat) := (1 : Real) / (2 * k + 1) * ((1 / (2 * ↑(m + 1) + 1)) ^ 2) ^ k
  change HasSum (fun k => f (k + 1)) _
  rw [hasSum_nat_add_iff]
  convert! (hasSum_log_one_add_inv m.cast_add_one_pos).mul_left ((↑(m + 1) : Real) + 1 / 2) using 1
  · ext k
    dsimp only [f]
    rw [← pow_mul]; 

中文:
定理 log_stirlingSeq_sdiff_hasSum
  条件: (m : 自然数)
  证明: by
  let f (k : Nat) := (1 : Real) / (2 * k + 1) * ((1 / (2 * ↑(m + 1) + 1)) ^ 2) ^ k
  change HasSum (fun k => f (k + 1)) _
  rw [hasSum_nat_add_iff]
  convert! (hasSum_log_one_add_inv m.cast_add_one_pos).mul_left ((↑(m + 1) : Real) + 1 / 2) using 1
  · ext k
    dsimp only [f]
    rw [← pow_mul]; 

Depends on / 依赖: HasSum, cast_add_one_pos, cast_mul, cast_s, convert, factorial_succ, hasSum_log_one_add_inv, hasSum_nat_add_iff, log_div, log_exp, log_mul, log_stirlingSeq_formula, m.cast_add_one_pos, mul_left, pow_add, pow_mul
-/
theorem log_stirlingSeq_sdiff_hasSum (m : Nat) :
    HasSum (fun k : Nat => (1 : Real) / (2 * ↑(k + 1) + 1) * ((1 / (2 * ↑(m + 1) + 1)) ^ 2) ^ ↑(k + 1))
      (log (stirlingSeq (m + 1)) - log (stirlingSeq (m + 2))) := by
  let f (k : Nat) := (1 : Real) / (2 * k + 1) * ((1 / (2 * ↑(m + 1) + 1)) ^ 2) ^ k
  change HasSum (fun k => f (k + 1)) _
  rw [hasSum_nat_add_iff]
  convert! (hasSum_log_one_add_inv m.cast_add_one_pos).mul_left ((↑(m + 1) : Real) + 1 / 2) using 1
  · ext k
    dsimp only [f]
    rw [← pow_mul]; rw [pow_add]
    push_cast
    field
  · have h (x) (hx : x != (0 : Real)) : 1 + x⁻¹ = (x + 1) / x := by field
    simp (disch := positivity) only [log_stirlingSeq_formula, log_div, log_mul, log_exp,
      factorial_succ, cast_mul, cast_succ, range_one, sum_singleton, h]
    ring

@[deprecated (since := "2026-06-03")]
alias log_stirlingSeq_diff_hasSum := log_stirlingSeq_sdiff_hasSum

/--
theorem `log_stirlingSeq'_antitone` / 定理 `log_stirlingSeq'_antitone`

English:
theorem log_stirlingSeq'_antitone
  statement: Antitone (Real.log ∘ stirlingSeq ∘ succ)
  proof: antitone_nat_of_succ_le fun n =>
sub_nonneg.mp (log_stirlingSeq_sdiff_hasSum n).nonneg fun m => by positivity

中文:
定理 log_stirlingSeq'_antitone
  结论: Antitone (实数.log ∘ stirlingSeq ∘ succ)
  证明: antitone_nat_of_succ_le fun n =>
sub_nonneg.mp (log_stirlingSeq_sdiff_hasSum n).nonneg fun m => by positivity

Depends on / 依赖: antitone_nat_of_succ_le, log_stirlingSeq_sdiff_hasSum, nonneg, sub_nonneg, sub_nonneg.mp
-/
theorem log_stirlingSeq'_antitone : Antitone (Real.log ∘ stirlingSeq ∘ succ) :=
  antitone_nat_of_succ_le fun n =>
sub_nonneg.mp (log_stirlingSeq_sdiff_hasSum n).nonneg fun m => by positivity

/-- We have a bound for successive elements in the sequence `log (stirlingSeq k)`. -/
@[deprecated "Use `log_stirlingSeq_sdiff_le` instead." (since := "2026-03-16")]
/--
theorem `log_stirlingSeq_sdiff_le_geo_sum` / 定理 `log_stirlingSeq_sdiff_le_geo_sum`

English:
theorem log_stirlingSeq_sdiff_le_geo_sum
  given: (n : Nat)
  proof: by
  have h_nonneg : (0 : Real) <= ((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2 := sq_nonneg _
  have g : HasSum (fun k : Nat => (((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2) ^ ↑(k + 1))
      (((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2 / (1 - ((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2)) := by
    have := (hasSum_geometri

中文:
定理 log_stirlingSeq_sdiff_le_geo_sum
  条件: (n : 自然数)
  证明: by
  have h_nonneg : (0 : Real) <= ((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2 := sq_nonneg _
  have g : HasSum (fun k : Nat => (((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2) ^ ↑(k + 1))
      (((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2 / (1 - ((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2)) := by
    have := (hasSum_geometri

Depends on / 依赖: Category, Category.assoc, HasSum, _root_, _root_.pow_succ, e.hom, e.inv, h_nonneg, hasSum_geometric_of_lt_one, hom_inv_id, inv_hom_id, inv_pow, lt_add_of_pos_left, mul_app_assoc, mul_left, one_div, pow_succ, simp_rw, smul_eq, sq_nonneg
-/
theorem log_stirlingSeq_sdiff_le_geo_sum (n : Nat) :
    log (stirlingSeq (n + 1)) - log (stirlingSeq (n + 2)) <=
      ((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2 / (1 - ((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2) := by
  have h_nonneg : (0 : Real) <= ((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2 := sq_nonneg _
  have g : HasSum (fun k : Nat => (((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2) ^ ↑(k + 1))
      (((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2 / (1 - ((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2)) := by
    have := (hasSum_geometric_of_lt_one h_nonneg ?_).mul_left (((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2)
    · simp_rw [← _root_.pow_succ'] at this
      exact this
    rw [one_div]; rw [inv_pow]
    exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (lt_add_of_pos_left _ <| by positivity) two_ne_zero)
  have hab (k : Nat) : (1 : Real) / (2 * ↑(k + 1) + 1) * ((1 / (2 * ↑(n + 1) + 1)) ^ 2) ^ ↑(k + 1) <=
      (((1 : Real) / (2 * ↑(n + 1) + 1)) ^ 2) ^ ↑(k + 1) := by
    refine mul_le_of_le_one_left (pow_nonneg h_nonneg ↑(k + 1)) ?_
    rw [one_div]
    exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left <| by positivity)
  exact hasSum_le hab (log_stirlingSeq_sdiff_hasSum n) g

@[deprecated (since := "2026-06-03")]
alias log_stirlingSeq_diff_le_geo_sum := log_stirlingSeq_sdiff_le_geo_sum

/--
theorem `log_stirlingSeq_sdiff_le` / 定理 `log_stirlingSeq_sdiff_le`

English:
theorem log_stirlingSeq_sdiff_le
  given: (n : Nat)
  proof: by
  rcases n with (_ | n)
  · suffices 0 <= Real.log (Real.exp 1 / Real.sqrt 2) by simpa
    apply Real.log_nonneg
    grw [one_le_div (by positivity), Real.sqrt_le_left (by positivity), ← Real.add_one_le_exp]
    norm_num
  set r := ((1 : Real) / (2 * (n + 1) + 1)) ^ 2 with hr
  have hr1 : r < 1 :

中文:
定理 log_stirlingSeq_sdiff_le
  条件: (n : 自然数)
  证明: by
  rcases n with (_ | n)
  · suffices 0 <= Real.log (Real.exp 1 / Real.sqrt 2) by simpa
    apply Real.log_nonneg
    grw [one_le_div (by positivity), Real.sqrt_le_left (by positivity), ← Real.add_one_le_exp]
    norm_num
  set r := ((1 : Real) / (2 * (n + 1) + 1)) ^ 2 with hr
  have hr1 : r < 1 :

Depends on / 依赖: HasSum, Real.add_one_le_exp, Real.exp, Real.log, Real.log_nonneg, Real.sqrt, Real.sqrt_le_left, add_one_le_exp, hasSum_le, log_nonneg, log_stirlingSeq_sdiff_hasSum, n.zero_le, one_le_div, sqrt_le_left, zero_le
-/
theorem log_stirlingSeq_sdiff_le (n : Nat) :
    log (stirlingSeq n) - log (stirlingSeq (n + 1)) <= 1 / (12 * n * (n + 1)) := by
  rcases n with (_ | n)
  · suffices 0 <= Real.log (Real.exp 1 / Real.sqrt 2) by simpa
    apply Real.log_nonneg
    grw [one_le_div (by positivity), Real.sqrt_le_left (by positivity), ← Real.add_one_le_exp]
    norm_num
  set r := ((1 : Real) / (2 * (n + 1) + 1)) ^ 2 with hr
  have hr1 : r < 1 := by grw [hr, ← n.zero_le]; norm_num
  suffices HasSum (fun j => r ^ (j + 1) / 3) ((1 : Real) / (12 * (n + 1 : Nat) * ((n + 1 : Nat) + 1))) by
    refine hasSum_le (fun j => ?_) (log_stirlingSeq_sdiff_hasSum n) this
    simpa [hr, field] using show (3 : Real) <= 2 * (j + 1) + 1 by norm_cast; grind
  grind [((hasSum_geometric_of_lt_one (by positivity) hr1).mul_right r).div_const 3]

@[deprecated (since := "2026-06-03")] alias log_stirlingSeq_diff_le := log_stirlingSeq_sdiff_le

/-- We have the bound `log (stirlingSeq n) - log (stirlingSeq (n+1)) ≤ 1 / (4 n ^ 2)`. -/
@[deprecated "Use `log_stirlingSeq_sdiff_le` instead." (since := "2026-03-16")]
/--
theorem `log_stirlingSeq_sub_log_stirlingSeq_succ` / 定理 `log_stirlingSeq_sub_log_stirlingSeq_succ`

English:
theorem log_stirlingSeq_sub_log_stirlingSeq_succ
  given: (n : Nat)
  proof: by
  grw [log_stirlingSeq_sdiff_le]
  cases n <;> simp [field]; grind

中文:
定理 log_stirlingSeq_sub_log_stirlingSeq_succ
  条件: (n : 自然数)
  证明: by
  grw [log_stirlingSeq_sdiff_le]
  cases n <;> simp [field]; grind

Depends on / 依赖: log_stirlingSeq_sdiff_le
-/
theorem log_stirlingSeq_sub_log_stirlingSeq_succ (n : Nat) :
    log (stirlingSeq n) - log (stirlingSeq (n + 1)) <= 1 / (4 * n ^ 2) := by
  grw [log_stirlingSeq_sdiff_le]
  cases n <;> simp [field]; grind

/--
theorem `log_stirlingSeq_bounded_aux` / 定理 `log_stirlingSeq_bounded_aux`

English:
theorem log_stirlingSeq_bounded_aux
  given: (n : Nat)
  proof: by
  let f (k : Nat) : Real := log (stirlingSeq (k + 1))
  let g (k : Nat) : Real := 1 / (12 * (k + 1))
  have hf k (hk : k in range n) : f k - (f (k + 1)) <= g k - g (k + 1) := by
    grw [log_stirlingSeq_sdiff_le]
    simp [field]
  replace hf := Finset.sum_le_sum hf
  rw [Finset.sum_range_sub']; 

中文:
定理 log_stirlingSeq_bounded_aux
  条件: (n : 自然数)
  证明: by
  let f (k : Nat) : Real := log (stirlingSeq (k + 1))
  let g (k : Nat) : Real := 1 / (12 * (k + 1))
  have hf k (hk : k in range n) : f k - (f (k + 1)) <= g k - g (k + 1) := by
    grw [log_stirlingSeq_sdiff_le]
    simp [field]
  replace hf := Finset.sum_le_sum hf
  rw [Finset.sum_range_sub']; 

Depends on / 依赖: Finset, Finset.sum_le_sum, Finset.sum_range_sub, log_stirlingSeq_sdiff_le, replace, stirlingSeq, sum_le_sum, sum_range_sub, zero_add
-/
theorem log_stirlingSeq_bounded_aux (n : Nat) :
    log (stirlingSeq 1) - log (stirlingSeq (n + 1)) <= 12⁻¹ := by
  let f (k : Nat) : Real := log (stirlingSeq (k + 1))
  let g (k : Nat) : Real := 1 / (12 * (k + 1))
  have hf k (hk : k in range n) : f k - (f (k + 1)) <= g k - g (k + 1) := by
    grw [log_stirlingSeq_sdiff_le]
    simp [field]
  replace hf := Finset.sum_le_sum hf
  rw [Finset.sum_range_sub']; rw [Finset.sum_range_sub'] at hf
  simp only [f, g, zero_add] at hf
  grw [hf]
  simp
  grind

/--
theorem `log_stirlingSeq_bounded_by_constant` / 定理 `log_stirlingSeq_bounded_by_constant`

English:
theorem log_stirlingSeq_bounded_by_constant
  given: (n : Nat)
  proof: by
  have := log_stirlingSeq_bounded_aux n
  rw [stirlingSeq_one]; rw [log_div (by positivity)]; rw [log_exp]; rw [log_sqrt] at this <;> grind

中文:
定理 log_stirlingSeq_bounded_by_constant
  条件: (n : 自然数)
  证明: by
  have := log_stirlingSeq_bounded_aux n
  rw [stirlingSeq_one]; rw [log_div (by positivity)]; rw [log_exp]; rw [log_sqrt] at this <;> grind

Depends on / 依赖: log_div, log_exp, log_sqrt, log_stirlingSeq_bounded_aux, stirlingSeq_one
-/
theorem log_stirlingSeq_bounded_by_constant (n : Nat) :
    1 - 12⁻¹ - log 2 / 2 <= log (stirlingSeq (n + 1)) := by
  have := log_stirlingSeq_bounded_aux n
  rw [stirlingSeq_one]; rw [log_div (by positivity)]; rw [log_exp]; rw [log_sqrt] at this <;> grind

/--
theorem `stirlingSeq'_pos` / 定理 `stirlingSeq'_pos`

English:
theorem stirlingSeq'_pos
  given: (n : Nat)
  statement: 0 < stirlingSeq (n + 1)
  proof: by unfold stirlingSeq; positivity

中文:
定理 stirlingSeq'_pos
  条件: (n : 自然数)
  结论: 0 < stirlingSeq (n + 1)
  证明: by unfold stirlingSeq; positivity

Depends on / 依赖: stirlingSeq
-/
theorem stirlingSeq'_pos (n : Nat) : 0 < stirlingSeq (n + 1) := by unfold stirlingSeq; positivity

/--
theorem `stirlingSeq'_bounded_by_pos_constant` / 定理 `stirlingSeq'_bounded_by_pos_constant`

English:
theorem stirlingSeq'_bounded_by_pos_constant
  statement: exists a, 0 < a ∧ forall n : Nat, a <= stirlingSeq (n + 1)
  proof: by
  let c := 1 - 12⁻¹ - log 2 / 2
  have h := log_stirlingSeq_bounded_by_constant
  refine ⟨exp c, exp_pos _, fun n => ?_⟩
  rw [← le_log_iff_exp_le (stirlingSeq'_pos n)]
  exact h n

中文:
定理 stirlingSeq'_bounded_by_pos_constant
  结论: 存在 a, 0 < a ∧ 对任意 n : 自然数, a <= stirlingSeq (n + 1)
  证明: by
  let c := 1 - 12⁻¹ - log 2 / 2
  have h := log_stirlingSeq_bounded_by_constant
  refine ⟨exp c, exp_pos _, fun n => ?_⟩
  rw [← le_log_iff_exp_le (stirlingSeq'_pos n)]
  exact h n
-/
theorem stirlingSeq'_bounded_by_pos_constant : exists a, 0 < a ∧ forall n : Nat, a <= stirlingSeq (n + 1) := by
  let c := 1 - 12⁻¹ - log 2 / 2
  have h := log_stirlingSeq_bounded_by_constant
  refine ⟨exp c, exp_pos _, fun n => ?_⟩
  rw [← le_log_iff_exp_le (stirlingSeq'_pos n)]
  exact h n

/--
theorem `stirlingSeq'_antitone` / 定理 `stirlingSeq'_antitone`

English:
theorem stirlingSeq'_antitone
  statement: Antitone (stirlingSeq ∘ succ)
  proof: fun n m h =>
  (log_le_log_iff (stirlingSeq'_pos m) (stirlingSeq'_pos n)).mp (log_stirlingSeq'_antitone h)

中文:
定理 stirlingSeq'_antitone
  结论: Antitone (stirlingSeq ∘ succ)
  证明: fun n m h =>
  (log_le_log_iff (stirlingSeq'_pos m) (stirlingSeq'_pos n)).mp (log_stirlingSeq'_antitone h)
-/
theorem stirlingSeq'_antitone : Antitone (stirlingSeq ∘ succ) := fun n m h =>
  (log_le_log_iff (stirlingSeq'_pos m) (stirlingSeq'_pos n)).mp (log_stirlingSeq'_antitone h)

/--
theorem `stirlingSeq_has_pos_limit_a` / 定理 `stirlingSeq_has_pos_limit_a`

English:
theorem stirlingSeq_has_pos_limit_a
  statement: exists a : Real, 0 < a ∧ Tendsto stirlingSeq atTop (𝓝 a)
  proof: by
  obtain ⟨x, x_pos, hx⟩ := stirlingSeq'_bounded_by_pos_constant
  have hx' : x in lowerBounds (Set.range (stirlingSeq ∘ succ)) := by simpa [lowerBounds] using hx
  refine ⟨_, lt_of_lt_of_le x_pos (le_csInf (Set.range_nonempty _) hx'), ?_⟩
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  exact tendst

中文:
定理 stirlingSeq_has_pos_limit_a
  结论: 存在 a : 实数, 0 < a ∧ Tendsto stirlingSeq atTop (𝓝 a)
  证明: by
  obtain ⟨x, x_pos, hx⟩ := stirlingSeq'_bounded_by_pos_constant
  have hx' : x in lowerBounds (Set.range (stirlingSeq ∘ succ)) := by simpa [lowerBounds] using hx
  refine ⟨_, lt_of_lt_of_le x_pos (le_csInf (Set.range_nonempty _) hx'), ?_⟩
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  exact tendst

Depends on / 依赖: Filter, Filter.tendsto_add_atTop_iff_nat, Set.range, Set.range_nonempty, _antitone, _bounded_by_pos_constant, le_csInf, lowerBounds, lt_of_lt_of_le, range_nonempty, stirlingSeq, tendsto_add_atTop_iff_nat, tendsto_atTop_ciInf, x_pos
-/
theorem stirlingSeq_has_pos_limit_a : exists a : Real, 0 < a ∧ Tendsto stirlingSeq atTop (𝓝 a) := by
  obtain ⟨x, x_pos, hx⟩ := stirlingSeq'_bounded_by_pos_constant
  have hx' : x in lowerBounds (Set.range (stirlingSeq ∘ succ)) := by simpa [lowerBounds] using hx
  refine ⟨_, lt_of_lt_of_le x_pos (le_csInf (Set.range_nonempty _) hx'), ?_⟩
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  exact tendsto_atTop_ciInf stirlingSeq'_antitone ⟨x, hx'⟩

/-!
### Part 2
https://proofwiki.org/wiki/Stirling%27s_Formula#Part_2
-/


/--
theorem `tendsto_self_div_two_mul_self_add_one` / 定理 `tendsto_self_div_two_mul_self_add_one`

English:
theorem tendsto_self_div_two_mul_self_add_one
  proof: by
  conv =>
    congr
    · skip
    · skip
    rw [one_div]; rw [← add_zero (2 : Real)]
  refine (((tendsto_const_div_atTop_nhds_zero_nat 1).const_add (2 : Real)).inv₀
    ((add_zero (2 : Real)).symm ▸ two_ne_zero)).congr' (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  rw [add_div' (1 : Real) 2 n (c

中文:
定理 tendsto_self_div_two_mul_self_add_one
  证明: by
  conv =>
    congr
    · skip
    · skip
    rw [one_div]; rw [← add_zero (2 : Real)]
  refine (((tendsto_const_div_atTop_nhds_zero_nat 1).const_add (2 : Real)).inv₀
    ((add_zero (2 : Real)).symm ▸ two_ne_zero)).congr' (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  rw [add_div' (1 : Real) 2 n (c

Depends on / 依赖: add_div, add_zero, cast_ne_zero, cast_ne_zero.mpr, const_add, eventually_atTop, eventually_atTop.mpr, inv_div, one_div, one_le_iff_ne_zero, one_le_iff_ne_zero.mp, tendsto_const_div_atTop_nhds_zero_nat, two_ne_zero
-/
theorem tendsto_self_div_two_mul_self_add_one :
    Tendsto (fun n : Nat => (n : Real) / (2 * n + 1)) atTop (𝓝 (1 / 2)) := by
  conv =>
    congr
    · skip
    · skip
    rw [one_div]; rw [← add_zero (2 : Real)]
  refine (((tendsto_const_div_atTop_nhds_zero_nat 1).const_add (2 : Real)).inv₀
    ((add_zero (2 : Real)).symm ▸ two_ne_zero)).congr' (eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
  rw [add_div' (1 : Real) 2 n (cast_ne_zero.mpr (one_le_iff_ne_zero.mp hn))]; rw [inv_div]

/--
theorem `stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq` / 定理 `stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq`

English:
theorem stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq
  given: (n : Nat) (hn : n != 0)
  proof: by
  have : 4 = 2 * 2 := by rfl
  rw [stirlingSeq]; rw [this]; rw [pow_mul]; rw [stirlingSeq]; rw [Wallis.W_eq_factorial_ratio]
  simp_rw [div_pow, mul_pow]
  rw [sq_sqrt]; rw [sq_sqrt]
  any_goals positivity
  simp [field, ← exp_nsmul]
  ring_nf

中文:
定理 stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq
  条件: (n : 自然数) (hn : n != 0)
  证明: by
  have : 4 = 2 * 2 := by rfl
  rw [stirlingSeq]; rw [this]; rw [pow_mul]; rw [stirlingSeq]; rw [Wallis.W_eq_factorial_ratio]
  simp_rw [div_pow, mul_pow]
  rw [sq_sqrt]; rw [sq_sqrt]
  any_goals positivity
  simp [field, ← exp_nsmul]
  ring_nf

Depends on / 依赖: W_eq_factorial_ratio, Wallis, Wallis.W_eq_factorial_ratio, any_goals, div_pow, exp_nsmul, mul_pow, pow_mul, ring_nf, simp_rw, sq_sqrt, stirlingSeq
-/
theorem stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq (n : Nat) (hn : n != 0) :
    stirlingSeq n ^ 4 / stirlingSeq (2 * n) ^ 2 * (n / (2 * n + 1)) = Wallis.W n := by
  have : 4 = 2 * 2 := by rfl
  rw [stirlingSeq]; rw [this]; rw [pow_mul]; rw [stirlingSeq]; rw [Wallis.W_eq_factorial_ratio]
  simp_rw [div_pow, mul_pow]
  rw [sq_sqrt]; rw [sq_sqrt]
  any_goals positivity
  simp [field, ← exp_nsmul]
  ring_nf

/--
theorem `second_wallis_limit` / 定理 `second_wallis_limit`

English:
theorem second_wallis_limit
  given: (a : Real) (hane : a != 0) (ha : Tendsto stirlingSeq atTop (𝓝 a))
  proof: by
  refine Tendsto.congr' (eventually_atTop.mpr ⟨1, fun n hn =>
    stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq n (one_le_iff_ne_zero.mp hn)⟩) ?_
  have h : a ^ 2 / 2 = a ^ 4 / a ^ 2 * (1 / 2) := by
    rw [mul_one_div]; rw [← mul_one_div (a ^ 4) (a ^ 2)]; rw [one_div]; rw [← pow_sub_of_lt a]
 

中文:
定理 second_wallis_limit
  条件: (a : 实数) (hane : a != 0) (ha : Tendsto stirlingSeq atTop (𝓝 a))
  证明: by
  refine Tendsto.congr' (eventually_atTop.mpr ⟨1, fun n hn =>
    stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq n (one_le_iff_ne_zero.mp hn)⟩) ?_
  have h : a ^ 2 / 2 = a ^ 4 / a ^ 2 * (1 / 2) := by
    rw [mul_one_div]; rw [← mul_one_div (a ^ 4) (a ^ 2)]; rw [one_div]; rw [← pow_sub_of_lt a]
 

Depends on / 依赖: Tendsto, Tendsto.congr, const_mul_atTop, eventually_atTop, eventually_atTop.mpr, ha.comp, ha.pow, mul_one_div, one_div, one_le_iff_ne_zero, one_le_iff_ne_zero.mp, pow_ne_zero, pow_sub_of_lt, stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq, tendsto_id, tendsto_id.const_mul_atTop, tendsto_self_div_two_mul_self_add_one, two_pos
-/
theorem second_wallis_limit (a : Real) (hane : a != 0) (ha : Tendsto stirlingSeq atTop (𝓝 a)) :
    Tendsto Wallis.W atTop (𝓝 (a ^ 2 / 2)) := by
  refine Tendsto.congr' (eventually_atTop.mpr ⟨1, fun n hn =>
    stirlingSeq_pow_four_div_stirlingSeq_pow_two_eq n (one_le_iff_ne_zero.mp hn)⟩) ?_
  have h : a ^ 2 / 2 = a ^ 4 / a ^ 2 * (1 / 2) := by
    rw [mul_one_div]; rw [← mul_one_div (a ^ 4) (a ^ 2)]; rw [one_div]; rw [← pow_sub_of_lt a]
    simp
  rw [h]
  exact ((ha.pow 4).div ((ha.comp (tendsto_id.const_mul_atTop' two_pos)).pow 2)
    (pow_ne_zero 2 hane)).mul tendsto_self_div_two_mul_self_add_one

/--
theorem `tendsto_stirlingSeq_sqrt_pi` / 定理 `tendsto_stirlingSeq_sqrt_pi`

English:
theorem tendsto_stirlingSeq_sqrt_pi
  statement: Tendsto stirlingSeq atTop (𝓝 (√π))
  proof: by
  obtain ⟨a, hapos, halimit⟩ := stirlingSeq_has_pos_limit_a
  have hπ : π / 2 = a ^ 2 / 2 :=
    tendsto_nhds_unique Wallis.tendsto_W_nhds_pi_div_two (second_wallis_limit a hapos.ne' halimit)
  rwa [(div_left_inj' (two_ne_zero' Real)).mp hπ, sqrt_sq hapos.le]

中文:
定理 tendsto_stirlingSeq_sqrt_pi
  结论: Tendsto stirlingSeq atTop (𝓝 (√π))
  证明: by
  obtain ⟨a, hapos, halimit⟩ := stirlingSeq_has_pos_limit_a
  have hπ : π / 2 = a ^ 2 / 2 :=
    tendsto_nhds_unique Wallis.tendsto_W_nhds_pi_div_two (second_wallis_limit a hapos.ne' halimit)
  rwa [(div_left_inj' (two_ne_zero' Real)).mp hπ, sqrt_sq hapos.le]

Depends on / 依赖: Wallis, Wallis.tendsto_W_nhds_pi_div_two, div_left_inj, halimit, hapos.le, hapos.ne, second_wallis_limit, sqrt_sq, stirlingSeq_has_pos_limit_a, tendsto_W_nhds_pi_div_two, tendsto_nhds_unique, two_ne_zero
-/
theorem tendsto_stirlingSeq_sqrt_pi : Tendsto stirlingSeq atTop (𝓝 (√π)) := by
  obtain ⟨a, hapos, halimit⟩ := stirlingSeq_has_pos_limit_a
  have hπ : π / 2 = a ^ 2 / 2 :=
    tendsto_nhds_unique Wallis.tendsto_W_nhds_pi_div_two (second_wallis_limit a hapos.ne' halimit)
  rwa [(div_left_inj' (two_ne_zero' Real)).mp hπ, sqrt_sq hapos.le]

/--
lemma `factorial_isEquivalent_stirling` / 引理 `factorial_isEquivalent_stirling`

English:
lemma factorial_isEquivalent_stirling
  proof: by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have : sqrt π != 0 := by positivity
  nth_rewrite 2 [← div_self this]
  convert! tendsto_stirlingSeq_sqrt_pi.div tendsto_const_nhds this using 1
  ext n
  simp [field, stirlingSeq, mul_right_comm]

中文:
引理 factorial_isEquivalent_stirling
  证明: by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have : sqrt π != 0 := by positivity
  nth_rewrite 2 [← div_self this]
  convert! tendsto_stirlingSeq_sqrt_pi.div tendsto_const_nhds this using 1
  ext n
  simp [field, stirlingSeq, mul_right_comm]

Depends on / 依赖: Asymptotics, Asymptotics.isEquivalent_of_tendsto_one, convert, div_self, isEquivalent_of_tendsto_one, mul_right_comm, nth_rewrite, stirlingSeq, tendsto_const_nhds, tendsto_stirlingSeq_sqrt_pi, tendsto_stirlingSeq_sqrt_pi.div
-/
lemma factorial_isEquivalent_stirling :
    (fun n => n ! : Nat -> Real) ~[atTop] fun n => Real.sqrt (2 * n * π) * (n / exp 1) ^ n := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have : sqrt π != 0 := by positivity
  nth_rewrite 2 [← div_self this]
  convert! tendsto_stirlingSeq_sqrt_pi.div tendsto_const_nhds this using 1
  ext n
  simp [field, stirlingSeq, mul_right_comm]

/-! ### Global bounds -/

/--
theorem `sqrt_pi_le_stirlingSeq` / 定理 `sqrt_pi_le_stirlingSeq`

English:
theorem sqrt_pi_le_stirlingSeq
  given: {n : Nat} (hn : n != 0)
  statement: √π <= stirlingSeq n
  proof: match n, hn with
  | n + 1, _ =>
stirlingSeq'_antitone.le_of_tendsto (b := n)
      tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)

中文:
定理 sqrt_pi_le_stirlingSeq
  条件: {n : 自然数} (hn : n != 0)
  结论: √π <= stirlingSeq n
  证明: match n, hn with
  | n + 1, _ =>
stirlingSeq'_antitone.le_of_tendsto (b := n)
      tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)

Depends on / 依赖: _antitone, _antitone.le_of_tendsto, le_of_tendsto, stirlingSeq, tendsto_add_atTop_nat, tendsto_stirlingSeq_sqrt_pi, tendsto_stirlingSeq_sqrt_pi.comp
-/
theorem sqrt_pi_le_stirlingSeq {n : Nat} (hn : n != 0) : √π <= stirlingSeq n :=
  match n, hn with
  | n + 1, _ =>
stirlingSeq'_antitone.le_of_tendsto (b := n)
      tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)

/--
theorem `le_factorial_stirling` / 定理 `le_factorial_stirling`

English:
theorem le_factorial_stirling
  given: (n : Nat)
  statement: √(2 * π * n) * (n / exp 1) ^ n <= n !
  proof: by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  have : √(2 * π * n) * (n / exp 1) ^ n = √π * (√(2 * n) * (n / exp 1) ^ n) := by
    simp [sqrt_mul']; ring
  rw [this]; rw [← le_div_iff₀ (by positivity)]
  exact sqrt_pi_le_stirlingSeq hn

中文:
定理 le_factorial_stirling
  条件: (n : 自然数)
  结论: √(2 * π * n) * (n / exp 1) ^ n <= n !
  证明: by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  have : √(2 * π * n) * (n / exp 1) ^ n = √π * (√(2 * n) * (n / exp 1) ^ n) := by
    simp [sqrt_mul']; ring
  rw [this]; rw [← le_div_iff₀ (by positivity)]
  exact sqrt_pi_le_stirlingSeq hn

Depends on / 依赖: eq_or_ne, sqrt_mul, sqrt_pi_le_stirlingSeq
-/
theorem le_factorial_stirling (n : Nat) : √(2 * π * n) * (n / exp 1) ^ n <= n ! := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  have : √(2 * π * n) * (n / exp 1) ^ n = √π * (√(2 * n) * (n / exp 1) ^ n) := by
    simp [sqrt_mul']; ring
  rw [this]; rw [← le_div_iff₀ (by positivity)]
  exact sqrt_pi_le_stirlingSeq hn

/--
theorem `le_log_factorial_stirling` / 定理 `le_log_factorial_stirling`

English:
theorem le_log_factorial_stirling
  given: {n : Nat} (hn : n != 0)
  proof: by
  calc
    _ = (log (2 * π) + log n) / 2 + n * (log n - 1) := by ring
    _ = log (√(2 * π * n) * (n / rexp 1) ^ n) := by
      rw [log_mul (x := √_)]; rw [log_sqrt]; rw [log_mul (x := 2 * π)]; rw [log_pow]; rw [log_div]; rw [log_exp] <;>
      positivity
    _ <= _ := log_le_log (by positivity) 

中文:
定理 le_log_factorial_stirling
  条件: {n : 自然数} (hn : n != 0)
  证明: by
  calc
    _ = (log (2 * π) + log n) / 2 + n * (log n - 1) := by ring
    _ = log (√(2 * π * n) * (n / rexp 1) ^ n) := by
      rw [log_mul (x := √_)]; rw [log_sqrt]; rw [log_mul (x := 2 * π)]; rw [log_pow]; rw [log_div]; rw [log_exp] <;>
      positivity
    _ <= _ := log_le_log (by positivity) 

Depends on / 依赖: le_factorial_stirling, log_div, log_exp, log_le_log, log_mul, log_pow, log_sqrt
-/
theorem le_log_factorial_stirling {n : Nat} (hn : n != 0) :
    n * log n - n + log n / 2 + log (2 * π) / 2 <= log n ! := by
  calc
    _ = (log (2 * π) + log n) / 2 + n * (log n - 1) := by ring
    _ = log (√(2 * π * n) * (n / rexp 1) ^ n) := by
      rw [log_mul (x := √_)]; rw [log_sqrt]; rw [log_mul (x := 2 * π)]; rw [log_pow]; rw [log_div]; rw [log_exp] <;>
      positivity
    _ <= _ := log_le_log (by positivity) (le_factorial_stirling n)

end Stirling
