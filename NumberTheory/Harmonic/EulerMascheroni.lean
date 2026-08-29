/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# The Euler-Mascheroni constant `γ`

We define the constant `γ`, and give upper and lower bounds for it.

## Main definitions and results

* `Real.eulerMascheroniConstant`: the constant `γ`
* `Real.tendsto_harmonic_sub_log`: the sequence `n ↦ harmonic n - log n` tends to `γ` as `n → ∞`
* `one_half_lt_eulerMascheroniConstant` and `eulerMascheroniConstant_lt_two_thirds`: upper and
  lower bounds.

## Outline of proofs

We show that

* the sequence `eulerMascheroniSeq` given by `n ↦ harmonic n - log (n + 1)` is strictly increasing;
* the sequence `eulerMascheroniSeq'` given by `n ↦ harmonic n - log n`, modified with a junk value
  for `n = 0`, is strictly decreasing;
* the difference `eulerMascheroniSeq' n - eulerMascheroniSeq n` is non-negative and tends to 0.

It follows that both sequences tend to a common limit `γ`, and we have the inequality
`eulerMascheroniSeq n < γ < eulerMascheroniSeq' n` for all `n`. Taking `n = 6` gives the bounds
`1 / 2 < γ < 2 / 3`.
-/

@[expose] public section

open Filter Topology

namespace Real

section LowerSequence

/--
Definition of `eulerMascheroniSeq` / `eulerMascheroniSeq` 的定义

English:
definition eulerMascheroniSeq
  signature: (n : Nat)
  body: harmonic n - log (n + 1)

中文:
定义 eulerMascheroniSeq
  签名: (n : 自然数)
  定义体: harmonic n - log (n + 1)

Depends on / 依赖: harmonic
-/
noncomputable def eulerMascheroniSeq (n : Nat) : Real := harmonic n - log (n + 1)

/--
lemma `eulerMascheroniSeq_zero` / 引理 `eulerMascheroniSeq_zero`

English:
lemma eulerMascheroniSeq_zero
  statement: eulerMascheroniSeq 0 = 0
  proof: by
  simp [eulerMascheroniSeq, harmonic_zero]

中文:
引理 eulerMascheroniSeq_zero
  结论: eulerMascheroniSeq 0 = 0
  证明: by
  simp [eulerMascheroniSeq, harmonic_zero]

Depends on / 依赖: eulerMascheroniSeq, harmonic_zero
-/
lemma eulerMascheroniSeq_zero : eulerMascheroniSeq 0 = 0 := by
  simp [eulerMascheroniSeq, harmonic_zero]

/--
lemma `strictMono_eulerMascheroniSeq` / 引理 `strictMono_eulerMascheroniSeq`

English:
lemma strictMono_eulerMascheroniSeq
  statement: StrictMono eulerMascheroniSeq
  proof: by
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  rw [eulerMascheroniSeq]; rw [eulerMascheroniSeq]; rw [← sub_pos]; rw [sub_sub_sub_comm]; rw [harmonic_succ]; rw [add_comm]; rw [Rat.cast_add]; rw [add_sub_cancel_right]; rw [← log_div (by positivity) (by positivity)]; rw [add_div]; rw [Nat.cast_add_one]; rw [Nat.cast_add_one]; rw [div_self (by positivity)]; rw [sub_pos]; rw [one_div]; rw [Rat.cast_inv]; rw [Rat.cast_add]; rw [Rat.cast_one]; rw [Rat.cast_natCast]
  refine (log_lt_sub_one_of_pos ?_ (ne_of_gt <| lt_add_of_pos_right _ ?_)).trans_le (le_of_eq ?_)
  · positivity
  · positivity
  · simp only [add_sub_cancel_left]

中文:
引理 strictMono_eulerMascheroniSeq
  结论: 严格递增 eulerMascheroniSeq
  证明: by
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  rw [eulerMascheroniSeq]; rw [eulerMascheroniSeq]; rw [← sub_pos]; rw [sub_sub_sub_comm]; rw [harmonic_succ]; rw [add_comm]; rw [Rat.cast_add]; rw [add_sub_cancel_right]; rw [← log_div (by positivity) (by positivity)]; rw [add_div]; rw [Nat.cast_add_one]; rw [Nat.cast_add_one]; rw [div_self (by positivity)]; rw [sub_pos]; rw [one_div]; rw [Rat.cast_inv]; rw [Rat.cast_add]; rw [Rat.cast_one]; rw [Rat.cast_natCast]
  refine (log_lt_sub_one_of_pos ?_ (ne_of_gt <| lt_add_of_pos_right _ ?_)).trans_le (le_of_eq ?_)
  · positivity
  · positivity
  · simp only [add_sub_cancel_left]

Depends on / 依赖: Nat.cast_add_one, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Rat.cast_one, add_comm, add_div, add_sub_cancel_right, cast_add, cast_add_one, cast_inv, cast_natCast, cast_one, div_self, eulerMascheroniSeq, harmonic_succ, log_div, log_lt_sub_one_of_pos, one_div, strictMono_nat_of_lt_succ
-/
lemma strictMono_eulerMascheroniSeq : StrictMono eulerMascheroniSeq := by
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  rw [eulerMascheroniSeq]; rw [eulerMascheroniSeq]; rw [← sub_pos]; rw [sub_sub_sub_comm]; rw [harmonic_succ]; rw [add_comm]; rw [Rat.cast_add]; rw [add_sub_cancel_right]; rw [← log_div (by positivity) (by positivity)]; rw [add_div]; rw [Nat.cast_add_one]; rw [Nat.cast_add_one]; rw [div_self (by positivity)]; rw [sub_pos]; rw [one_div]; rw [Rat.cast_inv]; rw [Rat.cast_add]; rw [Rat.cast_one]; rw [Rat.cast_natCast]
  refine (log_lt_sub_one_of_pos ?_ (ne_of_gt <| lt_add_of_pos_right _ ?_)).trans_le (le_of_eq ?_)
  · positivity
  · positivity
  · simp only [add_sub_cancel_left]

/--
lemma `one_half_lt_eulerMascheroniSeq_six` / 引理 `one_half_lt_eulerMascheroniSeq_six`

English:
lemma one_half_lt_eulerMascheroniSeq_six
  statement: 1 / 2 < eulerMascheroniSeq 6
  proof: by
  have : eulerMascheroniSeq 6 = 49 / 20 - log 7 := by
    rw [eulerMascheroniSeq]
    norm_num
  rw [this]; rw [lt_sub_iff_add_lt]; rw [← lt_sub_iff_add_lt']; rw [log_lt_iff_lt_exp (by positivity)]
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 7)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

中文:
引理 one_half_lt_eulerMascheroniSeq_six
  结论: 1 / 2 < eulerMascheroniSeq 6
  证明: by
  have : eulerMascheroniSeq 6 = 49 / 20 - log 7 := by
    rw [eulerMascheroniSeq]
    norm_num
  rw [this]; rw [lt_sub_iff_add_lt]; rw [← lt_sub_iff_add_lt']; rw [log_lt_iff_lt_exp (by positivity)]
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 7)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

Depends on / 依赖: Finset, Finset.sum_range_succ, Nat.factorial_succ, Real.sum_le_exp_of_nonneg, eulerMascheroniSeq, factorial_succ, log_lt_iff_lt_exp, lt_of_lt_of_le, lt_sub_iff_add_lt, simp_rw, sum_le_exp_of_nonneg, sum_range_succ
-/
lemma one_half_lt_eulerMascheroniSeq_six : 1 / 2 < eulerMascheroniSeq 6 := by
  have : eulerMascheroniSeq 6 = 49 / 20 - log 7 := by
    rw [eulerMascheroniSeq]
    norm_num
  rw [this]; rw [lt_sub_iff_add_lt]; rw [← lt_sub_iff_add_lt']; rw [log_lt_iff_lt_exp (by positivity)]
  refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 7)
  simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
  norm_num

end LowerSequence

section UpperSequence

/--
Definition of `eulerMascheroniSeq'` / `eulerMascheroniSeq'` 的定义

English:
definition eulerMascheroniSeq'
  signature: (n : Nat)
  body: if n = 0 then 2 else ↑(harmonic n) - log n

中文:
定义 eulerMascheroniSeq'
  签名: (n : 自然数)
  定义体: if n = 0 then 2 else ↑(harmonic n) - log n

Depends on / 依赖: harmonic
-/
noncomputable def eulerMascheroniSeq' (n : Nat) : Real :=
  if n = 0 then 2 else ↑(harmonic n) - log n

/--
lemma `eulerMascheroniSeq'_one` / 引理 `eulerMascheroniSeq'_one`

English:
lemma eulerMascheroniSeq'_one
  statement: eulerMascheroniSeq' 1 = 1
  proof: by
  simp [eulerMascheroniSeq']

中文:
引理 eulerMascheroniSeq'_one
  结论: eulerMascheroniSeq' 1 = 1
  证明: by
  simp [eulerMascheroniSeq']
-/
lemma eulerMascheroniSeq'_one : eulerMascheroniSeq' 1 = 1 := by
  simp [eulerMascheroniSeq']

/--
lemma `strictAnti_eulerMascheroniSeq'` / 引理 `strictAnti_eulerMascheroniSeq'`

English:
lemma strictAnti_eulerMascheroniSeq'
  statement: StrictAnti eulerMascheroniSeq'
  proof: by
  refine strictAnti_nat_of_succ_lt (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [eulerMascheroniSeq']
  simp_rw [eulerMascheroniSeq', eq_false_intro hn.ne', reduceCtorEq, if_false]
  rw [← sub_pos]; rw [sub_sub_sub_comm]; rw [harmonic_succ]; rw [Rat.cast_add]; rw [← sub_sub]; rw [sub_self]; rw [zero_sub]; rw [sub_eq_add_neg]; rw [neg_sub]; rw [← sub_eq_neg_add]; rw [sub_pos]; rw [← log_div (by positivity) (by positivity)]; rw [← neg_lt_neg_iff]; rw [← log_inv]
  refine (log_lt_sub_one_of_pos ?_ ?_).trans_le (le_of_eq ?_)
  · positivity
  · simp [field]
  · simp [field]

中文:
引理 strictAnti_eulerMascheroniSeq'
  结论: 严格递减 eulerMascheroniSeq'
  证明: by
  refine strictAnti_nat_of_succ_lt (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [eulerMascheroniSeq']
  simp_rw [eulerMascheroniSeq', eq_false_intro hn.ne', reduceCtorEq, if_false]
  rw [← sub_pos]; rw [sub_sub_sub_comm]; rw [harmonic_succ]; rw [Rat.cast_add]; rw [← sub_sub]; rw [sub_self]; rw [zero_sub]; rw [sub_eq_add_neg]; rw [neg_sub]; rw [← sub_eq_neg_add]; rw [sub_pos]; rw [← log_div (by positivity) (by positivity)]; rw [← neg_lt_neg_iff]; rw [← log_inv]
  refine (log_lt_sub_one_of_pos ?_ ?_).trans_le (le_of_eq ?_)
  · positivity
  · simp [field]
  · simp [field]

Depends on / 依赖: Nat.eq_zero_or_pos, Rat.cast_add, cast_add, eq_false_intro, eq_zero_or_pos, eulerMascheroniSeq, harmonic_succ, hn.ne, if_false, log_div, log_inv, log_lt_sub_o, neg_lt_neg_iff, neg_sub, reduceCtorEq, simp_rw, strictAnti_nat_of_succ_lt, sub_eq_add_neg, sub_eq_neg_add, sub_pos
-/
lemma strictAnti_eulerMascheroniSeq' : StrictAnti eulerMascheroniSeq' := by
  refine strictAnti_nat_of_succ_lt (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [eulerMascheroniSeq']
  simp_rw [eulerMascheroniSeq', eq_false_intro hn.ne', reduceCtorEq, if_false]
  rw [← sub_pos]; rw [sub_sub_sub_comm]; rw [harmonic_succ]; rw [Rat.cast_add]; rw [← sub_sub]; rw [sub_self]; rw [zero_sub]; rw [sub_eq_add_neg]; rw [neg_sub]; rw [← sub_eq_neg_add]; rw [sub_pos]; rw [← log_div (by positivity) (by positivity)]; rw [← neg_lt_neg_iff]; rw [← log_inv]
  refine (log_lt_sub_one_of_pos ?_ ?_).trans_le (le_of_eq ?_)
  · positivity
  · simp [field]
  · simp [field]

/--
lemma `eulerMascheroniSeq'_six_lt_two_thirds` / 引理 `eulerMascheroniSeq'_six_lt_two_thirds`

English:
lemma eulerMascheroniSeq'_six_lt_two_thirds
  statement: eulerMascheroniSeq' 6 < 2 / 3
  proof: by
  have h1 : eulerMascheroniSeq' 6 = 49 / 20 - log 6 := by
    rw [eulerMascheroniSeq']
    norm_num
  rw [h1]; rw [sub_lt_iff_lt_add]; rw [← sub_lt_iff_lt_add']; rw [lt_log_iff_exp_lt (by positivity)]
  norm_num
  have := rpow_lt_rpow (exp_pos _).le exp_one_lt_d9 (by simp : (0 : Real) < 107 / 60)
  rw [exp_one_rpow] at this
  refine lt_trans this ?_
  rw [← rpow_lt_rpow_iff (z := 60)]; rw [← rpow_mul]; rw [div_mul_cancel₀]; rw [← Nat.cast_ofNat]; rw [← Nat.cast_ofNat]; rw [rpow_natCast]; rw [Nat.cast_ofNat]; rw [← Nat.cast_ofNat (n := 60)]; rw [rpow_natCast]
  · norm_num
  all_goals positivity

中文:
引理 eulerMascheroniSeq'_six_lt_two_thirds
  结论: eulerMascheroniSeq' 6 < 2 / 3
  证明: by
  have h1 : eulerMascheroniSeq' 6 = 49 / 20 - log 6 := by
    rw [eulerMascheroniSeq']
    norm_num
  rw [h1]; rw [sub_lt_iff_lt_add]; rw [← sub_lt_iff_lt_add']; rw [lt_log_iff_exp_lt (by positivity)]
  norm_num
  have := rpow_lt_rpow (exp_pos _).le exp_one_lt_d9 (by simp : (0 : Real) < 107 / 60)
  rw [exp_one_rpow] at this
  refine lt_trans this ?_
  rw [← rpow_lt_rpow_iff (z := 60)]; rw [← rpow_mul]; rw [div_mul_cancel₀]; rw [← Nat.cast_ofNat]; rw [← Nat.cast_ofNat]; rw [rpow_natCast]; rw [Nat.cast_ofNat]; rw [← Nat.cast_ofNat (n := 60)]; rw [rpow_natCast]
  · norm_num
  all_goals positivity
-/
lemma eulerMascheroniSeq'_six_lt_two_thirds : eulerMascheroniSeq' 6 < 2 / 3 := by
  have h1 : eulerMascheroniSeq' 6 = 49 / 20 - log 6 := by
    rw [eulerMascheroniSeq']
    norm_num
  rw [h1]; rw [sub_lt_iff_lt_add]; rw [← sub_lt_iff_lt_add']; rw [lt_log_iff_exp_lt (by positivity)]
  norm_num
  have := rpow_lt_rpow (exp_pos _).le exp_one_lt_d9 (by simp : (0 : Real) < 107 / 60)
  rw [exp_one_rpow] at this
  refine lt_trans this ?_
  rw [← rpow_lt_rpow_iff (z := 60)]; rw [← rpow_mul]; rw [div_mul_cancel₀]; rw [← Nat.cast_ofNat]; rw [← Nat.cast_ofNat]; rw [rpow_natCast]; rw [Nat.cast_ofNat]; rw [← Nat.cast_ofNat (n := 60)]; rw [rpow_natCast]
  · norm_num
  all_goals positivity

/--
lemma `eulerMascheroniSeq_lt_eulerMascheroniSeq'` / 引理 `eulerMascheroniSeq_lt_eulerMascheroniSeq'`

English:
lemma eulerMascheroniSeq_lt_eulerMascheroniSeq'
  given: (m n : Nat)
  proof: by
  have (r : Nat) : eulerMascheroniSeq r < eulerMascheroniSeq' r := by
    rcases eq_zero_or_pos r with rfl | hr
    · simp [eulerMascheroniSeq, eulerMascheroniSeq']
    simp only [eulerMascheroniSeq, eulerMascheroniSeq', hr.ne', if_false]
    gcongr
    linarith
  apply (strictMono_eulerMascheroniSeq.monotone (le_max_left m n)).trans_lt
  exact (this _).trans_le (strictAnti_eulerMascheroniSeq'.antitone (le_max_right m n))

中文:
引理 eulerMascheroniSeq_lt_eulerMascheroniSeq'
  条件: (m n : 自然数)
  证明: by
  have (r : Nat) : eulerMascheroniSeq r < eulerMascheroniSeq' r := by
    rcases eq_zero_or_pos r with rfl | hr
    · simp [eulerMascheroniSeq, eulerMascheroniSeq']
    simp only [eulerMascheroniSeq, eulerMascheroniSeq', hr.ne', if_false]
    gcongr
    linarith
  apply (strictMono_eulerMascheroniSeq.monotone (le_max_left m n)).trans_lt
  exact (this _).trans_le (strictAnti_eulerMascheroniSeq'.antitone (le_max_right m n))

Depends on / 依赖: antitone, eq_zero_or_pos, eulerMascheroniSeq, hr.ne, if_false, le_max_left, le_max_right, monotone, strictAnti_eulerMascheroniSeq, strictMono_eulerMascheroniSeq, strictMono_eulerMascheroniSeq.monotone, trans_le, trans_lt
-/
lemma eulerMascheroniSeq_lt_eulerMascheroniSeq' (m n : Nat) :
    eulerMascheroniSeq m < eulerMascheroniSeq' n := by
  have (r : Nat) : eulerMascheroniSeq r < eulerMascheroniSeq' r := by
    rcases eq_zero_or_pos r with rfl | hr
    · simp [eulerMascheroniSeq, eulerMascheroniSeq']
    simp only [eulerMascheroniSeq, eulerMascheroniSeq', hr.ne', if_false]
    gcongr
    linarith
  apply (strictMono_eulerMascheroniSeq.monotone (le_max_left m n)).trans_lt
  exact (this _).trans_le (strictAnti_eulerMascheroniSeq'.antitone (le_max_right m n))

end UpperSequence

/--
Definition of `eulerMascheroniConstant` / `eulerMascheroniConstant` 的定义

English:
definition eulerMascheroniConstant
  signature: : Real
  body: limUnder atTop eulerMascheroniSeq

中文:
定义 eulerMascheroniConstant
  签名: : 实数
  定义体: limUnder atTop eulerMascheroniSeq

Depends on / 依赖: eulerMascheroniSeq, limUnder
-/
noncomputable def eulerMascheroniConstant : Real := limUnder atTop eulerMascheroniSeq

/--
lemma `tendsto_eulerMascheroniSeq` / 引理 `tendsto_eulerMascheroniSeq`

English:
lemma tendsto_eulerMascheroniSeq
  proof: by
  have := tendsto_atTop_ciSup strictMono_eulerMascheroniSeq.monotone ?_
  · rwa [eulerMascheroniConstant, this.limUnder_eq]
  · exact ⟨_, fun _ ⟨_, hn⟩ => hn ▸ (eulerMascheroniSeq_lt_eulerMascheroniSeq' _ 1).le⟩

中文:
引理 tendsto_eulerMascheroniSeq
  证明: by
  have := tendsto_atTop_ciSup strictMono_eulerMascheroniSeq.monotone ?_
  · rwa [eulerMascheroniConstant, this.limUnder_eq]
  · exact ⟨_, fun _ ⟨_, hn⟩ => hn ▸ (eulerMascheroniSeq_lt_eulerMascheroniSeq' _ 1).le⟩

Depends on / 依赖: eulerMascheroniConstant, eulerMascheroniSeq_lt_eulerMascheroniSeq, limUnder_eq, monotone, strictMono_eulerMascheroniSeq, strictMono_eulerMascheroniSeq.monotone, tendsto_atTop_ciSup, this.limUnder_eq
-/
lemma tendsto_eulerMascheroniSeq :
    Tendsto eulerMascheroniSeq atTop (𝓝 eulerMascheroniConstant) := by
  have := tendsto_atTop_ciSup strictMono_eulerMascheroniSeq.monotone ?_
  · rwa [eulerMascheroniConstant, this.limUnder_eq]
  · exact ⟨_, fun _ ⟨_, hn⟩ => hn ▸ (eulerMascheroniSeq_lt_eulerMascheroniSeq' _ 1).le⟩

/--
lemma `tendsto_harmonic_sub_log_add_one` / 引理 `tendsto_harmonic_sub_log_add_one`

English:
lemma tendsto_harmonic_sub_log_add_one
  proof: tendsto_eulerMascheroniSeq

中文:
引理 tendsto_harmonic_sub_log_add_one
  证明: tendsto_eulerMascheroniSeq

Depends on / 依赖: tendsto_eulerMascheroniSeq
-/
lemma tendsto_harmonic_sub_log_add_one :
    Tendsto (fun n : Nat => harmonic n - log (n + 1)) atTop (𝓝 eulerMascheroniConstant) :=
  tendsto_eulerMascheroniSeq

/--
lemma `tendsto_eulerMascheroniSeq'` / 引理 `tendsto_eulerMascheroniSeq'`

English:
lemma tendsto_eulerMascheroniSeq'
  proof: by
  suffices Tendsto (fun n => eulerMascheroniSeq' n - eulerMascheroniSeq n) atTop (𝓝 0) by
    simpa using this.add tendsto_eulerMascheroniSeq
  suffices Tendsto (fun x : Real => log (x + 1) - log x) atTop (𝓝 0) by
    apply (this.comp tendsto_natCast_atTop_atTop).congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [eulerMascheroniSeq, eulerMascheroniSeq', eq_false_intro hn]
  exact tendsto_log_comp_add_sub_log 1

中文:
引理 tendsto_eulerMascheroniSeq'
  证明: by
  suffices Tendsto (fun n => eulerMascheroniSeq' n - eulerMascheroniSeq n) atTop (𝓝 0) by
    simpa using this.add tendsto_eulerMascheroniSeq
  suffices Tendsto (fun x : Real => log (x + 1) - log x) atTop (𝓝 0) by
    apply (this.comp tendsto_natCast_atTop_atTop).congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [eulerMascheroniSeq, eulerMascheroniSeq', eq_false_intro hn]
  exact tendsto_log_comp_add_sub_log 1

Depends on / 依赖: Tendsto, eq_false_intro, eulerMascheroniSeq, eventually_ne_atTop, filter_upwards, tendsto_eulerMascheroniSeq, tendsto_log_comp_add_sub_log, tendsto_natCast_atTop_atTop, this.add, this.comp
-/
lemma tendsto_eulerMascheroniSeq' :
    Tendsto eulerMascheroniSeq' atTop (𝓝 eulerMascheroniConstant) := by
  suffices Tendsto (fun n => eulerMascheroniSeq' n - eulerMascheroniSeq n) atTop (𝓝 0) by
    simpa using this.add tendsto_eulerMascheroniSeq
  suffices Tendsto (fun x : Real => log (x + 1) - log x) atTop (𝓝 0) by
    apply (this.comp tendsto_natCast_atTop_atTop).congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp [eulerMascheroniSeq, eulerMascheroniSeq', eq_false_intro hn]
  exact tendsto_log_comp_add_sub_log 1

/--
lemma `tendsto_harmonic_sub_log` / 引理 `tendsto_harmonic_sub_log`

English:
lemma tendsto_harmonic_sub_log
  proof: by
  apply tendsto_eulerMascheroniSeq'.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp_rw [eulerMascheroniSeq', hn, if_false]

中文:
引理 tendsto_harmonic_sub_log
  证明: by
  apply tendsto_eulerMascheroniSeq'.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp_rw [eulerMascheroniSeq', hn, if_false]

Depends on / 依赖: eulerMascheroniSeq, eventually_ne_atTop, filter_upwards, if_false, simp_rw, tendsto_eulerMascheroniSeq
-/
lemma tendsto_harmonic_sub_log :
    Tendsto (fun n : Nat => harmonic n - log n) atTop (𝓝 eulerMascheroniConstant) := by
  apply tendsto_eulerMascheroniSeq'.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp_rw [eulerMascheroniSeq', hn, if_false]

/--
lemma `eulerMascheroniSeq_lt_eulerMascheroniConstant` / 引理 `eulerMascheroniSeq_lt_eulerMascheroniConstant`

English:
lemma eulerMascheroniSeq_lt_eulerMascheroniConstant
  given: (n : Nat)
  proof: by
  refine (strictMono_eulerMascheroniSeq (Nat.lt_succ_self n)).trans_le ?_
  apply strictMono_eulerMascheroniSeq.monotone.ge_of_tendsto tendsto_eulerMascheroniSeq

中文:
引理 eulerMascheroniSeq_lt_eulerMascheroniConstant
  条件: (n : 自然数)
  证明: by
  refine (strictMono_eulerMascheroniSeq (Nat.lt_succ_self n)).trans_le ?_
  apply strictMono_eulerMascheroniSeq.monotone.ge_of_tendsto tendsto_eulerMascheroniSeq

Depends on / 依赖: Nat.lt_succ_self, ge_of_tendsto, lt_succ_self, monotone, strictMono_eulerMascheroniSeq, strictMono_eulerMascheroniSeq.monotone.ge_of_tendsto, tendsto_eulerMascheroniSeq, trans_le
-/
lemma eulerMascheroniSeq_lt_eulerMascheroniConstant (n : Nat) :
    eulerMascheroniSeq n < eulerMascheroniConstant := by
  refine (strictMono_eulerMascheroniSeq (Nat.lt_succ_self n)).trans_le ?_
  apply strictMono_eulerMascheroniSeq.monotone.ge_of_tendsto tendsto_eulerMascheroniSeq

/--
lemma `eulerMascheroniConstant_lt_eulerMascheroniSeq'` / 引理 `eulerMascheroniConstant_lt_eulerMascheroniSeq'`

English:
lemma eulerMascheroniConstant_lt_eulerMascheroniSeq'
  given: (n : Nat)
  proof: by
  refine lt_of_le_of_lt ?_ (strictAnti_eulerMascheroniSeq' (Nat.lt_succ_self n))
  apply strictAnti_eulerMascheroniSeq'.antitone.le_of_tendsto tendsto_eulerMascheroniSeq'

中文:
引理 eulerMascheroniConstant_lt_eulerMascheroniSeq'
  条件: (n : 自然数)
  证明: by
  refine lt_of_le_of_lt ?_ (strictAnti_eulerMascheroniSeq' (Nat.lt_succ_self n))
  apply strictAnti_eulerMascheroniSeq'.antitone.le_of_tendsto tendsto_eulerMascheroniSeq'

Depends on / 依赖: Nat.lt_succ_self, antitone, antitone.le_of_tendsto, le_of_tendsto, lt_of_le_of_lt, lt_succ_self, strictAnti_eulerMascheroniSeq, tendsto_eulerMascheroniSeq
-/
lemma eulerMascheroniConstant_lt_eulerMascheroniSeq' (n : Nat) :
    eulerMascheroniConstant < eulerMascheroniSeq' n := by
  refine lt_of_le_of_lt ?_ (strictAnti_eulerMascheroniSeq' (Nat.lt_succ_self n))
  apply strictAnti_eulerMascheroniSeq'.antitone.le_of_tendsto tendsto_eulerMascheroniSeq'

/--
lemma `one_half_lt_eulerMascheroniConstant` / 引理 `one_half_lt_eulerMascheroniConstant`

English:
lemma one_half_lt_eulerMascheroniConstant
  statement: 1 / 2 < eulerMascheroniConstant
  proof: one_half_lt_eulerMascheroniSeq_six.trans (eulerMascheroniSeq_lt_eulerMascheroniConstant _)

中文:
引理 one_half_lt_eulerMascheroniConstant
  结论: 1 / 2 < eulerMascheroniConstant
  证明: one_half_lt_eulerMascheroniSeq_six.trans (eulerMascheroniSeq_lt_eulerMascheroniConstant _)

Depends on / 依赖: eulerMascheroniSeq_lt_eulerMascheroniConstant, one_half_lt_eulerMascheroniSeq_six, one_half_lt_eulerMascheroniSeq_six.trans
-/
lemma one_half_lt_eulerMascheroniConstant : 1 / 2 < eulerMascheroniConstant :=
  one_half_lt_eulerMascheroniSeq_six.trans (eulerMascheroniSeq_lt_eulerMascheroniConstant _)

/--
lemma `eulerMascheroniConstant_lt_two_thirds` / 引理 `eulerMascheroniConstant_lt_two_thirds`

English:
lemma eulerMascheroniConstant_lt_two_thirds
  statement: eulerMascheroniConstant < 2 / 3
  proof: (eulerMascheroniConstant_lt_eulerMascheroniSeq' _).trans eulerMascheroniSeq'_six_lt_two_thirds

中文:
引理 eulerMascheroniConstant_lt_two_thirds
  结论: eulerMascheroniConstant < 2 / 3
  证明: (eulerMascheroniConstant_lt_eulerMascheroniSeq' _).trans eulerMascheroniSeq'_six_lt_two_thirds

Depends on / 依赖: _six_lt_two_thirds, eulerMascheroniConstant_lt_eulerMascheroniSeq, eulerMascheroniSeq
-/
lemma eulerMascheroniConstant_lt_two_thirds : eulerMascheroniConstant < 2 / 3 :=
  (eulerMascheroniConstant_lt_eulerMascheroniSeq' _).trans eulerMascheroniSeq'_six_lt_two_thirds

end Real
