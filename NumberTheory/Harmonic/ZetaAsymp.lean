/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Terence Tao
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Mathlib.Analysis.Asymptotics.Lemmas

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Asymptotics of `ζ s` as `s → 1` or `s → 0`

The goal of this file is to evaluate the limit of `ζ s - 1 / (s - 1)` as `s → 1`.

### Main results

* `tendsto_riemannZeta_sub_one_div`: the limit of `ζ s - 1 / (s - 1)`, at the filter of punctured
  neighbourhoods of 1 in `ℂ`, exists and is equal to the Euler-Mascheroni constant `γ`.
* `deriv_riemannZeta_zero`: `ζ'(0) = -log(2π) / 2`, which derives from the above.
* `riemannZeta_one_ne_zero`: with our definition of `ζ 1` (which is characterised as the limit of
  `ζ s - 1 / (s - 1) / Gammaℝ s` as `s → 1`), we have `ζ 1 ≠ 0`.
* Representation of `riemannZeta s` as `(s-1)⁻¹ + riemannZeta₀ s` or `(s-1)⁻¹ * riemannZeta₁ s`
  for certain entire functions `riemannZeta₀` and `riemannZeta₁`.
* Asymptotics for `deriv riemannZeta s`, `log (riemannZeta s)`,
  `(deriv riemannZeta s) / (riemannZeta s)` and `(riemannZeta s)⁻¹` as `s → 1`.
* `riemannZeta_conj`: the conjugation symmetry `ζ (conj s) = conj (ζ s)` (valid for all `s`,
  since the junk value `ζ 1` is real).

### Outline of arguments

We consider the sum `F s = ∑' n : ℕ, f (n + 1) s`, where `s` is a real variable and
`f n s = ∫ x in n..(n + 1), (x - n) / x ^ (s + 1)`. We show that `F s` is continuous on `[1, ∞)`,
that `F 1 = 1 - γ`, and that `F s = 1 / (s - 1) - ζ s / s` for `1 < s`.

By combining these formulae, one deduces that the limit of `ζ s - 1 / (s - 1)` at `𝓝[>] (1 : ℝ)`
exists and is equal to `γ`. Finally, using this and the Riemann removable singularity criterion
we obtain the limit along punctured neighbourhoods of 1 in `ℂ`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

@[inherit_doc] local notation "γ" => Real.eulerMascheroniConstant

namespace ZetaAsymptotics

-- since the intermediate lemmas are of little interest in themselves we put them in a namespace

open Real

/-!
## Definitions
-/

/--
Definition of `term` / `term` 的定义

English:
definition term
  signature: (n : Nat) (s : Real)
  body: ∫ x : Real in n..(n + 1), (x - n) / x ^ (s + 1)

中文:
定义 term
  签名: (n : 自然数) (s : 实数)
  定义体: ∫ x : Real in n..(n + 1), (x - n) / x ^ (s + 1)
-/
noncomputable def term (n : Nat) (s : Real) : Real := ∫ x : Real in n..(n + 1), (x - n) / x ^ (s + 1)

/--
Definition of `termSum` / `termSum` 的定义

English:
definition termSum
  signature: (s : Real) (N : Nat)
  body: ∑ n in Finset.range N, term (n + 1) s

中文:
定义 termSum
  签名: (s : 实数) (N : 自然数)
  定义体: ∑ n in Finset.range N, term (n + 1) s

Depends on / 依赖: Finset, Finset.range
-/
noncomputable def termSum (s : Real) (N : Nat) : Real := ∑ n in Finset.range N, term (n + 1) s

/--
Definition of `termTSum` / `termTSum` 的定义

English:
definition termTSum
  signature: (s : Real)
  body: ∑' n, term (n + 1) s

@[deprecated (since := "2026-05-27")] alias term_sum := termSum
@[deprecated (since := "2026-05-27")] alias term_tsum := termTSum

中文:
定义 termTSum
  签名: (s : 实数)
  定义体: ∑' n, term (n + 1) s

@[deprecated (since := "2026-05-27")] alias term_sum := termSum
@[deprecated (since := "2026-05-27")] alias term_tsum := termTSum
-/
noncomputable def termTSum (s : Real) : Real := ∑' n, term (n + 1) s

@[deprecated (since := "2026-05-27")] alias term_sum := termSum
@[deprecated (since := "2026-05-27")] alias term_tsum := termTSum

/--
lemma `term_nonneg` / 引理 `term_nonneg`

English:
lemma term_nonneg
  given: (n : Nat) (s : Real)
  statement: 0 <= term n s
  proof: by
  rw [term]; rw [intervalIntegral.integral_of_le (by simp)]
  refine setIntegral_nonneg measurableSet_Ioc (fun x hx => ?_)
  refine div_nonneg ?_ (rpow_nonneg ?_ _)
  all_goals linarith [hx.1]

中文:
引理 term_nonneg
  条件: (n : 自然数) (s : 实数)
  结论: 0 <= term n s
  证明: by
  rw [term]; rw [intervalIntegral.integral_of_le (by simp)]
  refine setIntegral_nonneg measurableSet_Ioc (fun x hx => ?_)
  refine div_nonneg ?_ (rpow_nonneg ?_ _)
  all_goals linarith [hx.1]

Depends on / 依赖: all_goals, div_nonneg, integral_of_le, intervalIntegral, intervalIntegral.integral_of_le, measurableSet_Ioc, rpow_nonneg, setIntegral_nonneg
-/
lemma term_nonneg (n : Nat) (s : Real) : 0 <= term n s := by
  rw [term]; rw [intervalIntegral.integral_of_le (by simp)]
  refine setIntegral_nonneg measurableSet_Ioc (fun x hx => ?_)
  refine div_nonneg ?_ (rpow_nonneg ?_ _)
  all_goals linarith [hx.1]

/--
lemma `term_welldef` / 引理 `term_welldef`

English:
lemma term_welldef
  given: {n : Nat} (hn : 0 < n) {s : Real} (hs : 0 < s)
  proof: by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
  refine (continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ?_ ?_ ?_).integrableOn_Icc
  · fun_prop
  · apply continuousAt_id.rpow_const (Or.inr <| by linarith)
  · exact (rpow_pos_of_pos ((Nat.cast_pos.mpr hn).trans_le hx.1) _).ne'

中文:
引理 term_welldef
  条件: {n : 自然数} (hn : 0 < n) {s : 实数} (hs : 0 < s)
  证明: by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
  refine (continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ?_ ?_ ?_).integrableOn_Icc
  · fun_prop
  · apply continuousAt_id.rpow_const (Or.inr <| by linarith)
  · exact (rpow_pos_of_pos ((Nat.cast_pos.mpr hn).trans_le hx.1) _).ne'

Depends on / 依赖: ContinuousAt, ContinuousAt.div, Nat.cast_pos.mpr, Or.inr, cast_pos, continuousAt_id, continuousAt_id.rpow_const, continuousOn_of_forall_continuousAt, fun_prop, integrableOn_Icc, intervalIntegrable_iff_integrableOn_Icc_of_le, rpow_const, rpow_pos_of_pos, trans_le
-/
lemma term_welldef {n : Nat} (hn : 0 < n) {s : Real} (hs : 0 < s) :
    IntervalIntegrable (fun x : Real => (x - n) / x ^ (s + 1)) volume n (n + 1) := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
  refine (continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ?_ ?_ ?_).integrableOn_Icc
  · fun_prop
  · apply continuousAt_id.rpow_const (Or.inr <| by linarith)
  · exact (rpow_pos_of_pos ((Nat.cast_pos.mpr hn).trans_le hx.1) _).ne'

section s_eq_one


/--
lemma `term_one` / 引理 `term_one`

English:
lemma term_one
  given: {n : Nat} (hn : 0 < n)
  proof: by
  have hv : forall x in uIcc (n : Real) (n + 1), 0 < x := by
    intro x hx
    rw [uIcc_of_le (by simp only [le_add_iff_nonneg_right]; rw [zero_le_one])] at hx
    exact (Nat.cast_pos.mpr hn).trans_le hx.1
  calc term n 1
    _ = ∫ x : Real in n..(n + 1), (x - n) / x ^ 2 := by
      simp_rw [term, one_add_one_eq_two, ← Nat.cast_two (R := Real), rpow_natCast]
    _ = ∫ x : Real in n..(n + 1), (1 / x - n / x ^ 2) :=
      intervalIntegral.integral_congr (fun x hx => by field)
    _ = (∫ x : Real in n..(n + 1), 1 / x) - n * ∫ x : Real in n..(n + 1), 1 / x ^ 2 := by
      simp_rw [← mul_one_div (n : Real)]
      rw [intervalIntegral.integral_sub]
      · simp_rw [intervalIntegral.integral_const_mul]
      · exact intervalIntegral.intervalIntegrable_one_div (fun x hx => (hv x hx).ne') (by fun_prop)
      · exact (intervalIntegral.intervalIntegrable_one_div
          (fun x hx => (sq_pos_of_pos (hv x hx)).ne') (by fun_prop)).const_mul _
    _ = (log (↑n + 1) - log ↑n) - n * ∫ x : Real in n..(n + 1), 1 / x ^ 2 := by
      congr 1
      rw [integral_one_div_of_pos]; rw [log_div]
      all_goals positivity
    _ = (log (↑n + 1) - log ↑n) - n * ∫ x : Real in n..(n + 1), x ^ (-2 : Real) := by
      congr 2
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [rpow_neg]; rw [one_div]; rw [← Nat.cast_two (R := Real)]; rw [rpow_natCast]
      exact (hv x hx).le
    _ = log (↑n + 1) - log ↑n - n * (1 / n - 1 / (n + 1)) := by
      rw [integral_rpow]
      · simp_rw [sub_div, (by norm_num : (-2 : Real) + 1 = -1), div_neg, div_one, neg_sub_neg,
          rpow_neg_one, ← one_div]
      · refine Or.inr ⟨by simp, notMem_uIcc_of_lt ?_ ?_⟩
        all_goals positivity
    _ = log (↑n + 1) - log ↑n - 1 / (↑n + 1) := by
      congr 1
      simp [field]

中文:
引理 term_one
  条件: {n : 自然数} (hn : 0 < n)
  证明: by
  have hv : forall x in uIcc (n : Real) (n + 1), 0 < x := by
    intro x hx
    rw [uIcc_of_le (by simp only [le_add_iff_nonneg_right]; rw [zero_le_one])] at hx
    exact (Nat.cast_pos.mpr hn).trans_le hx.1
  calc term n 1
    _ = ∫ x : Real in n..(n + 1), (x - n) / x ^ 2 := by
      simp_rw [term, one_add_one_eq_two, ← Nat.cast_two (R := Real), rpow_natCast]
    _ = ∫ x : Real in n..(n + 1), (1 / x - n / x ^ 2) :=
      intervalIntegral.integral_congr (fun x hx => by field)
    _ = (∫ x : Real in n..(n + 1), 1 / x) - n * ∫ x : Real in n..(n + 1), 1 / x ^ 2 := by
      simp_rw [← mul_one_div (n : Real)]
      rw [intervalIntegral.integral_sub]
      · simp_rw [intervalIntegral.integral_const_mul]
      · exact intervalIntegral.intervalIntegrable_one_div (fun x hx => (hv x hx).ne') (by fun_prop)
      · exact (intervalIntegral.intervalIntegrable_one_div
          (fun x hx => (sq_pos_of_pos (hv x hx)).ne') (by fun_prop)).const_mul _
    _ = (log (↑n + 1) - log ↑n) - n * ∫ x : Real in n..(n + 1), 1 / x ^ 2 := by
      congr 1
      rw [integral_one_div_of_pos]; rw [log_div]
      all_goals positivity
    _ = (log (↑n + 1) - log ↑n) - n * ∫ x : Real in n..(n + 1), x ^ (-2 : Real) := by
      congr 2
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [rpow_neg]; rw [one_div]; rw [← Nat.cast_two (R := Real)]; rw [rpow_natCast]
      exact (hv x hx).le
    _ = log (↑n + 1) - log ↑n - n * (1 / n - 1 / (n + 1)) := by
      rw [integral_rpow]
      · simp_rw [sub_div, (by norm_num : (-2 : Real) + 1 = -1), div_neg, div_one, neg_sub_neg,
          rpow_neg_one, ← one_div]
      · refine Or.inr ⟨by simp, notMem_uIcc_of_lt ?_ ?_⟩
        all_goals positivity
    _ = log (↑n + 1) - log ↑n - 1 / (↑n + 1) := by
      congr 1
      simp [field]

Depends on / 依赖: Nat.cast_pos.mpr, Nat.cast_two, cast_pos, cast_two, integral_congr, intervalIntegral, intervalIntegral.integral_congr, le_add_iff_nonneg_right, one_add_one_eq_two, rpow_natCast, simp_rw, trans_le, uIcc_of_le, zero_le_one
-/
lemma term_one {n : Nat} (hn : 0 < n) :
    term n 1 = (log (n + 1) - log n) - 1 / (n + 1) := by
  have hv : forall x in uIcc (n : Real) (n + 1), 0 < x := by
    intro x hx
    rw [uIcc_of_le (by simp only [le_add_iff_nonneg_right]; rw [zero_le_one])] at hx
    exact (Nat.cast_pos.mpr hn).trans_le hx.1
  calc term n 1
    _ = ∫ x : Real in n..(n + 1), (x - n) / x ^ 2 := by
      simp_rw [term, one_add_one_eq_two, ← Nat.cast_two (R := Real), rpow_natCast]
    _ = ∫ x : Real in n..(n + 1), (1 / x - n / x ^ 2) :=
      intervalIntegral.integral_congr (fun x hx => by field)
    _ = (∫ x : Real in n..(n + 1), 1 / x) - n * ∫ x : Real in n..(n + 1), 1 / x ^ 2 := by
      simp_rw [← mul_one_div (n : Real)]
      rw [intervalIntegral.integral_sub]
      · simp_rw [intervalIntegral.integral_const_mul]
      · exact intervalIntegral.intervalIntegrable_one_div (fun x hx => (hv x hx).ne') (by fun_prop)
      · exact (intervalIntegral.intervalIntegrable_one_div
          (fun x hx => (sq_pos_of_pos (hv x hx)).ne') (by fun_prop)).const_mul _
    _ = (log (↑n + 1) - log ↑n) - n * ∫ x : Real in n..(n + 1), 1 / x ^ 2 := by
      congr 1
      rw [integral_one_div_of_pos]; rw [log_div]
      all_goals positivity
    _ = (log (↑n + 1) - log ↑n) - n * ∫ x : Real in n..(n + 1), x ^ (-2 : Real) := by
      congr 2
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [rpow_neg]; rw [one_div]; rw [← Nat.cast_two (R := Real)]; rw [rpow_natCast]
      exact (hv x hx).le
    _ = log (↑n + 1) - log ↑n - n * (1 / n - 1 / (n + 1)) := by
      rw [integral_rpow]
      · simp_rw [sub_div, (by norm_num : (-2 : Real) + 1 = -1), div_neg, div_one, neg_sub_neg,
          rpow_neg_one, ← one_div]
      · refine Or.inr ⟨by simp, notMem_uIcc_of_lt ?_ ?_⟩
        all_goals positivity
    _ = log (↑n + 1) - log ↑n - 1 / (↑n + 1) := by
      congr 1
      simp [field]

/--
lemma `termSum_one` / 引理 `termSum_one`

English:
lemma termSum_one
  given: (N : Nat)
  statement: termSum 1 N = log (N + 1) - harmonic (N + 1) + 1
  proof: by
  induction N with
  | zero =>
    simp_rw [termSum, Finset.sum_range_zero, harmonic_succ, harmonic_zero,
      Nat.cast_zero, zero_add, Nat.cast_one, inv_one, Rat.cast_one, log_one, sub_add_cancel]
  | succ N hN =>
    unfold termSum at hN ⊢
    rw [Finset.sum_range_succ]; rw [hN]; rw [harmonic_succ (N + 1)]; rw [term_one (by positivity : 0 < N + 1)]
    push_cast
    ring_nf

@[deprecated (since := "2026-05-27")] alias term_sum_one := termSum_one

中文:
引理 termSum_one
  条件: (N : 自然数)
  结论: termSum 1 N = log (N + 1) - harmonic (N + 1) + 1
  证明: by
  induction N with
  | zero =>
    simp_rw [termSum, Finset.sum_range_zero, harmonic_succ, harmonic_zero,
      Nat.cast_zero, zero_add, Nat.cast_one, inv_one, Rat.cast_one, log_one, sub_add_cancel]
  | succ N hN =>
    unfold termSum at hN ⊢
    rw [Finset.sum_range_succ]; rw [hN]; rw [harmonic_succ (N + 1)]; rw [term_one (by positivity : 0 < N + 1)]
    push_cast
    ring_nf

@[deprecated (since := "2026-05-27")] alias term_sum_one := termSum_one

Depends on / 依赖: Finset, Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_one, Nat.cast_zero, Rat.cast_one, cast_one, cast_zero, harmonic_succ, harmonic_zero, inv_one, log_one, ring_nf, simp_rw, sub_add_cancel, sum_range_succ, sum_range_zero, termSum, term_one, zero_add
-/
lemma termSum_one (N : Nat) : termSum 1 N = log (N + 1) - harmonic (N + 1) + 1 := by
  induction N with
  | zero =>
    simp_rw [termSum, Finset.sum_range_zero, harmonic_succ, harmonic_zero,
      Nat.cast_zero, zero_add, Nat.cast_one, inv_one, Rat.cast_one, log_one, sub_add_cancel]
  | succ N hN =>
    unfold termSum at hN ⊢
    rw [Finset.sum_range_succ]; rw [hN]; rw [harmonic_succ (N + 1)]; rw [term_one (by positivity : 0 < N + 1)]
    push_cast
    ring_nf

@[deprecated (since := "2026-05-27")] alias term_sum_one := termSum_one

/--
lemma `term_tsum_one` / 引理 `term_tsum_one`

English:
lemma term_tsum_one
  statement: HasSum (fun n => term (n + 1) 1) (1 - γ)
  proof: by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => term_nonneg (n + 1) 1)]
  change Tendsto (fun N => termSum 1 N) atTop _
  simp_rw [termSum_one, sub_eq_neg_add]
  refine Tendsto.add ?_ tendsto_const_nhds
  have := (tendsto_eulerMascheroniSeq'.comp (tendsto_add_atTop_nat 1)).neg
  refine this.congr' (Eventually.of_forall (fun n => ?_))
  simp_rw [Function.comp_apply, eulerMascheroniSeq', reduceCtorEq, if_false]
  push_cast
  abel

中文:
引理 term_tsum_one
  结论: HasSum (fun n => term (n + 1) 1) (1 - γ)
  证明: by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => term_nonneg (n + 1) 1)]
  change Tendsto (fun N => termSum 1 N) atTop _
  simp_rw [termSum_one, sub_eq_neg_add]
  refine Tendsto.add ?_ tendsto_const_nhds
  have := (tendsto_eulerMascheroniSeq'.comp (tendsto_add_atTop_nat 1)).neg
  refine this.congr' (Eventually.of_forall (fun n => ?_))
  simp_rw [Function.comp_apply, eulerMascheroniSeq', reduceCtorEq, if_false]
  push_cast
  abel

Depends on / 依赖: Eventually, Eventually.of_forall, Function, Function.comp_apply, Tendsto, Tendsto.add, comp_apply, eulerMascheroniSeq, hasSum_iff_tendsto_nat_of_nonneg, if_false, of_forall, reduceCtorEq, simp_rw, sub_eq_neg_add, tendsto_add_atTop_nat, tendsto_const_nhds, tendsto_eulerMascheroniSeq, termSum, termSum_one, term_nonneg
-/
lemma term_tsum_one : HasSum (fun n => term (n + 1) 1) (1 - γ) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => term_nonneg (n + 1) 1)]
  change Tendsto (fun N => termSum 1 N) atTop _
  simp_rw [termSum_one, sub_eq_neg_add]
  refine Tendsto.add ?_ tendsto_const_nhds
  have := (tendsto_eulerMascheroniSeq'.comp (tendsto_add_atTop_nat 1)).neg
  refine this.congr' (Eventually.of_forall (fun n => ?_))
  simp_rw [Function.comp_apply, eulerMascheroniSeq', reduceCtorEq, if_false]
  push_cast
  abel

end s_eq_one

section s_gt_one


/--
lemma `term_of_lt` / 引理 `term_of_lt`

English:
lemma term_of_lt
  given: {n : Nat} (hn : 0 < n) {s : Real} (hs : 1 < s)
  proof: by
  have hv : forall x in uIcc (n : Real) (n + 1), 0 < x := by
    intro x hx
    rw [uIcc_of_le (by simp only [le_add_iff_nonneg_right]; rw [zero_le_one])] at hx
    exact (Nat.cast_pos.mpr hn).trans_le hx.1
  calc term n s
    _ = ∫ x : Real in n..(n + 1), (x - n) / x ^ (s + 1) := by rfl
    _ = ∫ x : Real in n..(n + 1), (x ^ (-s) - n * x ^ (-(s + 1))) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [sub_div]; rw [rpow_add_one (hv x hx).ne']; rw [mul_comm]; rw [← div_div]; rw [div_self (hv x hx).ne']; rw [rpow_neg (hv x hx).le]; rw [rpow_neg (hv x hx).le]; rw [one_div]; rw [rpow_add_one (hv x hx).ne']; rw [mul_comm]; rw [div_eq_mul_inv]
    _ = (∫ x : Real in n..(n + 1), x ^ (-s)) - n * (∫ x : Real in n..(n + 1), x ^ (-(s + 1))) := by
      rw [intervalIntegral.integral_sub]; rw [intervalIntegral.integral_const_mul] <;>
      [skip; apply IntervalIntegrable.const_mul] <;>
      · refine intervalIntegral.intervalIntegrable_rpow (Or.inr <| notMem_uIcc_of_lt ?_ ?_)
        · exact_mod_cast hn
        · linarith
    _ = 1 / (s - 1) * (1 / n ^ (s - 1) - 1 / (n + 1) ^ (s - 1))
          - n / s * (1 / n ^ s - 1 / (n + 1) ^ s) := by
      have : 0 ∉ uIcc (n : Real) (n + 1) := (lt_irrefl _ <| hv _ ·)
      rw [integral_rpow (Or.inr ⟨by linarith]; rw [this⟩)]; rw [integral_rpow (Or.inr ⟨by linarith]; rw [this⟩)]
      congr 1
      · rw [show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div, mul_comm, mul_one_div, neg_sub,
          rpow_neg (Nat.cast_nonneg _), one_div, rpow_neg (by linarith), one_div]
      · rw [show -(s + 1) + 1 = -s by ring, div_neg, ← neg_div, neg_sub, div_mul_eq_mul_div,
          mul_div_assoc, rpow_neg (Nat.cast_nonneg _), one_div, rpow_neg (by linarith), one_div]

中文:
引理 term_of_lt
  条件: {n : 自然数} (hn : 0 < n) {s : 实数} (hs : 1 < s)
  证明: by
  have hv : forall x in uIcc (n : Real) (n + 1), 0 < x := by
    intro x hx
    rw [uIcc_of_le (by simp only [le_add_iff_nonneg_right]; rw [zero_le_one])] at hx
    exact (Nat.cast_pos.mpr hn).trans_le hx.1
  calc term n s
    _ = ∫ x : Real in n..(n + 1), (x - n) / x ^ (s + 1) := by rfl
    _ = ∫ x : Real in n..(n + 1), (x ^ (-s) - n * x ^ (-(s + 1))) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [sub_div]; rw [rpow_add_one (hv x hx).ne']; rw [mul_comm]; rw [← div_div]; rw [div_self (hv x hx).ne']; rw [rpow_neg (hv x hx).le]; rw [rpow_neg (hv x hx).le]; rw [one_div]; rw [rpow_add_one (hv x hx).ne']; rw [mul_comm]; rw [div_eq_mul_inv]
    _ = (∫ x : Real in n..(n + 1), x ^ (-s)) - n * (∫ x : Real in n..(n + 1), x ^ (-(s + 1))) := by
      rw [intervalIntegral.integral_sub]; rw [intervalIntegral.integral_const_mul] <;>
      [skip; apply IntervalIntegrable.const_mul] <;>
      · refine intervalIntegral.intervalIntegrable_rpow (Or.inr <| notMem_uIcc_of_lt ?_ ?_)
        · exact_mod_cast hn
        · linarith
    _ = 1 / (s - 1) * (1 / n ^ (s - 1) - 1 / (n + 1) ^ (s - 1))
          - n / s * (1 / n ^ s - 1 / (n + 1) ^ s) := by
      have : 0 ∉ uIcc (n : Real) (n + 1) := (lt_irrefl _ <| hv _ ·)
      rw [integral_rpow (Or.inr ⟨by linarith]; rw [this⟩)]; rw [integral_rpow (Or.inr ⟨by linarith]; rw [this⟩)]
      congr 1
      · rw [show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div, mul_comm, mul_one_div, neg_sub,
          rpow_neg (Nat.cast_nonneg _), one_div, rpow_neg (by linarith), one_div]
      · rw [show -(s + 1) + 1 = -s by ring, div_neg, ← neg_div, neg_sub, div_mul_eq_mul_div,
          mul_div_assoc, rpow_neg (Nat.cast_nonneg _), one_div, rpow_neg (by linarith), one_div]

Depends on / 依赖: Nat.cast_pos.mpr, cast_pos, div_div, div_self, integral_congr, intervalIntegral, intervalIntegral.integral_congr, le_add_iff_nonneg_right, mul_comm, rpow_add_one, sub_div, trans_le, uIcc_of_le, zero_le_one
-/
lemma term_of_lt {n : Nat} (hn : 0 < n) {s : Real} (hs : 1 < s) :
    term n s = 1 / (s - 1) * (1 / n ^ (s - 1) - 1 / (n + 1) ^ (s - 1))
    - n / s * (1 / n ^ s - 1 / (n + 1) ^ s) := by
  have hv : forall x in uIcc (n : Real) (n + 1), 0 < x := by
    intro x hx
    rw [uIcc_of_le (by simp only [le_add_iff_nonneg_right]; rw [zero_le_one])] at hx
    exact (Nat.cast_pos.mpr hn).trans_le hx.1
  calc term n s
    _ = ∫ x : Real in n..(n + 1), (x - n) / x ^ (s + 1) := by rfl
    _ = ∫ x : Real in n..(n + 1), (x ^ (-s) - n * x ^ (-(s + 1))) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [sub_div]; rw [rpow_add_one (hv x hx).ne']; rw [mul_comm]; rw [← div_div]; rw [div_self (hv x hx).ne']; rw [rpow_neg (hv x hx).le]; rw [rpow_neg (hv x hx).le]; rw [one_div]; rw [rpow_add_one (hv x hx).ne']; rw [mul_comm]; rw [div_eq_mul_inv]
    _ = (∫ x : Real in n..(n + 1), x ^ (-s)) - n * (∫ x : Real in n..(n + 1), x ^ (-(s + 1))) := by
      rw [intervalIntegral.integral_sub]; rw [intervalIntegral.integral_const_mul] <;>
      [skip; apply IntervalIntegrable.const_mul] <;>
      · refine intervalIntegral.intervalIntegrable_rpow (Or.inr <| notMem_uIcc_of_lt ?_ ?_)
        · exact_mod_cast hn
        · linarith
    _ = 1 / (s - 1) * (1 / n ^ (s - 1) - 1 / (n + 1) ^ (s - 1))
          - n / s * (1 / n ^ s - 1 / (n + 1) ^ s) := by
      have : 0 ∉ uIcc (n : Real) (n + 1) := (lt_irrefl _ <| hv _ ·)
      rw [integral_rpow (Or.inr ⟨by linarith]; rw [this⟩)]; rw [integral_rpow (Or.inr ⟨by linarith]; rw [this⟩)]
      congr 1
      · rw [show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div, mul_comm, mul_one_div, neg_sub,
          rpow_neg (Nat.cast_nonneg _), one_div, rpow_neg (by linarith), one_div]
      · rw [show -(s + 1) + 1 = -s by ring, div_neg, ← neg_div, neg_sub, div_mul_eq_mul_div,
          mul_div_assoc, rpow_neg (Nat.cast_nonneg _), one_div, rpow_neg (by linarith), one_div]

/--
lemma `termSum_of_lt` / 引理 `termSum_of_lt`

English:
lemma termSum_of_lt
  given: (N : Nat) {s : Real} (hs : 1 < s)
  proof: by
  simp only [termSum]
  conv => enter [1, 2, n]; rw [term_of_lt (by simp) hs]
  rw [Finset.sum_sub_distrib]
  congr 1
  · induction N with
    | zero => simp
    | succ N hN =>
      rw [Finset.sum_range_succ]; rw [hN]; rw [Nat.cast_add_one]
      ring_nf
  · simp_rw [mul_comm (_ / _), ← mul_div_assoc, div_eq_mul_inv _ s, ← Finset.sum_mul, mul_one]
    congr 1
    induction N with
    | zero => simp
    | succ N hN =>
      simp_rw [Finset.sum_range_succ, hN, Nat.cast_add_one, sub_eq_add_neg, add_assoc]
      congr 1
      ring_nf

@[deprecated (since := "2026-05-27")] alias term_sum_of_lt := termSum_of_lt

中文:
引理 termSum_of_lt
  条件: (N : 自然数) {s : 实数} (hs : 1 < s)
  证明: by
  simp only [termSum]
  conv => enter [1, 2, n]; rw [term_of_lt (by simp) hs]
  rw [Finset.sum_sub_distrib]
  congr 1
  · induction N with
    | zero => simp
    | succ N hN =>
      rw [Finset.sum_range_succ]; rw [hN]; rw [Nat.cast_add_one]
      ring_nf
  · simp_rw [mul_comm (_ / _), ← mul_div_assoc, div_eq_mul_inv _ s, ← Finset.sum_mul, mul_one]
    congr 1
    induction N with
    | zero => simp
    | succ N hN =>
      simp_rw [Finset.sum_range_succ, hN, Nat.cast_add_one, sub_eq_add_neg, add_assoc]
      congr 1
      ring_nf

@[deprecated (since := "2026-05-27")] alias term_sum_of_lt := termSum_of_lt

Depends on / 依赖: Finset, Finset.sum_mul, Finset.sum_range_succ, Finset.sum_sub_distrib, Nat.cast_add_one, add_assoc, cast_add_one, div_eq_mul_inv, mul_comm, mul_div_assoc, mul_one, ring_nf, simp_rw, sub_eq_add_neg, sum_mul, sum_range_succ, sum_sub_distrib, termSum, term_of_lt
-/
lemma termSum_of_lt (N : Nat) {s : Real} (hs : 1 < s) :
    termSum s N = 1 / (s - 1) * (1 - 1 / (N + 1) ^ (s - 1))
    - 1 / s * ((∑ n in Finset.range N, 1 / (n + 1 : Real) ^ s) - N / (N + 1) ^ s) := by
  simp only [termSum]
  conv => enter [1, 2, n]; rw [term_of_lt (by simp) hs]
  rw [Finset.sum_sub_distrib]
  congr 1
  · induction N with
    | zero => simp
    | succ N hN =>
      rw [Finset.sum_range_succ]; rw [hN]; rw [Nat.cast_add_one]
      ring_nf
  · simp_rw [mul_comm (_ / _), ← mul_div_assoc, div_eq_mul_inv _ s, ← Finset.sum_mul, mul_one]
    congr 1
    induction N with
    | zero => simp
    | succ N hN =>
      simp_rw [Finset.sum_range_succ, hN, Nat.cast_add_one, sub_eq_add_neg, add_assoc]
      congr 1
      ring_nf

@[deprecated (since := "2026-05-27")] alias term_sum_of_lt := termSum_of_lt

/--
lemma `termTSum_of_lt` / 引理 `termTSum_of_lt`

English:
lemma termTSum_of_lt
  given: {s : Real} (hs : 1 < s)
  proof: by
  apply HasSum.tsum_eq
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => term_nonneg (n + 1) s)]
  change Tendsto (fun N => termSum s N) atTop _
  simp_rw [termSum_of_lt _ hs]
  apply Tendsto.sub
  · rw [show 𝓝 (1 / (s - 1)) = 𝓝 (1 / (s - 1) - 1 / (s - 1) * 0) by simp]
    simp_rw [mul_sub, mul_one]
    refine tendsto_const_nhds.sub (Tendsto.const_mul _ ?_)
refine tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by linarith)).comp ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  · rw [← sub_zero (tsum _)]
    apply (((Summable.hasSum ?_).tendsto_sum_nat).sub ?_).const_mul
    · exact_mod_cast (summable_nat_add_iff 1).mpr (summable_one_div_nat_rpow.mpr hs)
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
              (h := fun n : Nat => (1 / ↑(n + 1) : Real) ^ (s - 1))
      · rw [show 𝓝 (0 : Real) = 𝓝 (0 ^ (s - 1)) by rw [zero_rpow]; linarith]
        refine Tendsto.rpow_const ?_ (Or.inr <| by linarith)
        exact (tendsto_const_div_atTop_nhds_zero_nat _).comp (tendsto_add_atTop_nat _)
      · intro n
        positivity
      · intro n
        dsimp only
        transitivity (n + 1) / (n + 1) ^ s
        · gcongr
          linarith
        · apply le_of_eq
          rw [rpow_sub_one]; rw [← div_mul]; rw [div_one]; rw [mul_comm]; rw [one_div]; rw [inv_rpow]; rw [← div_eq_mul_inv]
          · norm_cast
          all_goals positivity

@[deprecated (since := "2026-05-27")] alias term_tsum_of_lt := termTSum_of_lt

中文:
引理 termTSum_of_lt
  条件: {s : 实数} (hs : 1 < s)
  证明: by
  apply HasSum.tsum_eq
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => term_nonneg (n + 1) s)]
  change Tendsto (fun N => termSum s N) atTop _
  simp_rw [termSum_of_lt _ hs]
  apply Tendsto.sub
  · rw [show 𝓝 (1 / (s - 1)) = 𝓝 (1 / (s - 1) - 1 / (s - 1) * 0) by simp]
    simp_rw [mul_sub, mul_one]
    refine tendsto_const_nhds.sub (Tendsto.const_mul _ ?_)
refine tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by linarith)).comp ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  · rw [← sub_zero (tsum _)]
    apply (((Summable.hasSum ?_).tendsto_sum_nat).sub ?_).const_mul
    · exact_mod_cast (summable_nat_add_iff 1).mpr (summable_one_div_nat_rpow.mpr hs)
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
              (h := fun n : Nat => (1 / ↑(n + 1) : Real) ^ (s - 1))
      · rw [show 𝓝 (0 : Real) = 𝓝 (0 ^ (s - 1)) by rw [zero_rpow]; linarith]
        refine Tendsto.rpow_const ?_ (Or.inr <| by linarith)
        exact (tendsto_const_div_atTop_nhds_zero_nat _).comp (tendsto_add_atTop_nat _)
      · intro n
        positivity
      · intro n
        dsimp only
        transitivity (n + 1) / (n + 1) ^ s
        · gcongr
          linarith
        · apply le_of_eq
          rw [rpow_sub_one]; rw [← div_mul]; rw [div_one]; rw [mul_comm]; rw [one_div]; rw [inv_rpow]; rw [← div_eq_mul_inv]
          · norm_cast
          all_goals positivity

@[deprecated (since := "2026-05-27")] alias term_tsum_of_lt := termTSum_of_lt

Depends on / 依赖: HasSum, HasSum.tsum_eq, Tendsto, Tendsto.const_mul, Tendsto.sub, const_mul, div_atTop, hasSum_iff_tendsto_nat_of_nonneg, mul_one, mul_sub, simp_rw, tendsto_atTop_add_const_right, tendsto_const_nhds, tendsto_const_nhds.div_atTop, tendsto_const_nhds.sub, tendsto_natCast_atTop_atTop, tendsto_rpow_atTop, termSum, termSum_of_lt, term_nonneg
-/
lemma termTSum_of_lt {s : Real} (hs : 1 < s) :
    termTSum s = (1 / (s - 1) - 1 / s * ∑' n : Nat, 1 / (n + 1 : Real) ^ s) := by
  apply HasSum.tsum_eq
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => term_nonneg (n + 1) s)]
  change Tendsto (fun N => termSum s N) atTop _
  simp_rw [termSum_of_lt _ hs]
  apply Tendsto.sub
  · rw [show 𝓝 (1 / (s - 1)) = 𝓝 (1 / (s - 1) - 1 / (s - 1) * 0) by simp]
    simp_rw [mul_sub, mul_one]
    refine tendsto_const_nhds.sub (Tendsto.const_mul _ ?_)
refine tendsto_const_nhds.div_atTop (tendsto_rpow_atTop (by linarith)).comp ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  · rw [← sub_zero (tsum _)]
    apply (((Summable.hasSum ?_).tendsto_sum_nat).sub ?_).const_mul
    · exact_mod_cast (summable_nat_add_iff 1).mpr (summable_one_div_nat_rpow.mpr hs)
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
              (h := fun n : Nat => (1 / ↑(n + 1) : Real) ^ (s - 1))
      · rw [show 𝓝 (0 : Real) = 𝓝 (0 ^ (s - 1)) by rw [zero_rpow]; linarith]
        refine Tendsto.rpow_const ?_ (Or.inr <| by linarith)
        exact (tendsto_const_div_atTop_nhds_zero_nat _).comp (tendsto_add_atTop_nat _)
      · intro n
        positivity
      · intro n
        dsimp only
        transitivity (n + 1) / (n + 1) ^ s
        · gcongr
          linarith
        · apply le_of_eq
          rw [rpow_sub_one]; rw [← div_mul]; rw [div_one]; rw [mul_comm]; rw [one_div]; rw [inv_rpow]; rw [← div_eq_mul_inv]
          · norm_cast
          all_goals positivity

@[deprecated (since := "2026-05-27")] alias term_tsum_of_lt := termTSum_of_lt

/--
lemma `zeta_limit_aux1` / 引理 `zeta_limit_aux1`

English:
lemma zeta_limit_aux1
  given: {s : Real} (hs : 1 < s)
  proof: by
  rw [termTSum_of_lt hs]
  generalize (∑' n : Nat, 1 / (n + 1 : Real) ^ s) = Z
  field [(show s - 1 != 0 by linarith)]

中文:
引理 zeta_limit_aux1
  条件: {s : 实数} (hs : 1 < s)
  证明: by
  rw [termTSum_of_lt hs]
  generalize (∑' n : Nat, 1 / (n + 1 : Real) ^ s) = Z
  field [(show s - 1 != 0 by linarith)]

Depends on / 依赖: generalize, termTSum_of_lt
-/
lemma zeta_limit_aux1 {s : Real} (hs : 1 < s) :
    (∑' n : Nat, 1 / (n + 1 : Real) ^ s) - 1 / (s - 1) = 1 - s * termTSum s := by
  rw [termTSum_of_lt hs]
  generalize (∑' n : Nat, 1 / (n + 1 : Real) ^ s) = Z
  field [(show s - 1 != 0 by linarith)]

end s_gt_one

section continuity


/--
lemma `continuousOn_term` / 引理 `continuousOn_term`

English:
lemma continuousOn_term
  given: (n : Nat)
  proof: by
  -- TODO: can this be shortened using the lemma
  -- `continuous_parametric_intervalIntegral_of_continuous'` from https://github.com/leanprover-community/mathlib4/pull/11185?
  simp only [term, intervalIntegral.integral_of_le (by linarith : (↑(n + 1) : Real) <= ↑(n + 1) + 1)]
  apply continuousOn_of_dominated (bound := fun x => (x - ↑(n + 1)) / x ^ (2 : Real))
  · exact fun s hs => (term_welldef (by simp) (zero_lt_one.trans_le hs)).1.1
  · intro s (hs : 1 <= s)
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    have : 1 < x := lt_of_le_of_lt (by simp) hx.1
    rw [norm_of_nonneg (div_nonneg (sub_nonneg.mpr hx.1.le) (by positivity))]; rw [Nat.cast_add_one]
    gcongr
    · exact_mod_cast sub_nonneg.mpr hx.1.le
    · exact this.le
    · linarith
  · rw [← IntegrableOn, ← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact_mod_cast term_welldef (by lia : 0 < (n + 1)) zero_lt_one
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    refine continuousOn_of_forall_continuousAt (fun s (hs : 1 <= s) => continuousAt_const.div ?_ ?_)
    · exact continuousAt_const.rpow (continuousAt_id.add continuousAt_const) (Or.inr (by linarith))
    · exact (rpow_pos_of_pos ((Nat.cast_pos.mpr (by simp)).trans hx.1) _).ne'

中文:
引理 continuousOn_term
  条件: (n : 自然数)
  证明: by
  -- TODO: can this be shortened using the lemma
  -- `continuous_parametric_intervalIntegral_of_continuous'` from https://github.com/leanprover-community/mathlib4/pull/11185?
  simp only [term, intervalIntegral.integral_of_le (by linarith : (↑(n + 1) : Real) <= ↑(n + 1) + 1)]
  apply continuousOn_of_dominated (bound := fun x => (x - ↑(n + 1)) / x ^ (2 : Real))
  · exact fun s hs => (term_welldef (by simp) (zero_lt_one.trans_le hs)).1.1
  · intro s (hs : 1 <= s)
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    have : 1 < x := lt_of_le_of_lt (by simp) hx.1
    rw [norm_of_nonneg (div_nonneg (sub_nonneg.mpr hx.1.le) (by positivity))]; rw [Nat.cast_add_one]
    gcongr
    · exact_mod_cast sub_nonneg.mpr hx.1.le
    · exact this.le
    · linarith
  · rw [← IntegrableOn, ← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact_mod_cast term_welldef (by lia : 0 < (n + 1)) zero_lt_one
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    refine continuousOn_of_forall_continuousAt (fun s (hs : 1 <= s) => continuousAt_const.div ?_ ?_)
    · exact continuousAt_const.rpow (continuousAt_id.add continuousAt_const) (Or.inr (by linarith))
    · exact (rpow_pos_of_pos ((Nat.cast_pos.mpr (by simp)).trans hx.1) _).ne'
-/
lemma continuousOn_term (n : Nat) :
    ContinuousOn (fun x => term (n + 1) x) (Ici 1) := by
  -- TODO: can this be shortened using the lemma
  -- `continuous_parametric_intervalIntegral_of_continuous'` from https://github.com/leanprover-community/mathlib4/pull/11185?
  simp only [term, intervalIntegral.integral_of_le (by linarith : (↑(n + 1) : Real) <= ↑(n + 1) + 1)]
  apply continuousOn_of_dominated (bound := fun x => (x - ↑(n + 1)) / x ^ (2 : Real))
  · exact fun s hs => (term_welldef (by simp) (zero_lt_one.trans_le hs)).1.1
  · intro s (hs : 1 <= s)
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    have : 1 < x := lt_of_le_of_lt (by simp) hx.1
    rw [norm_of_nonneg (div_nonneg (sub_nonneg.mpr hx.1.le) (by positivity))]; rw [Nat.cast_add_one]
    gcongr
    · exact_mod_cast sub_nonneg.mpr hx.1.le
    · exact this.le
    · linarith
  · rw [← IntegrableOn, ← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact_mod_cast term_welldef (by lia : 0 < (n + 1)) zero_lt_one
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    refine continuousOn_of_forall_continuousAt (fun s (hs : 1 <= s) => continuousAt_const.div ?_ ?_)
    · exact continuousAt_const.rpow (continuousAt_id.add continuousAt_const) (Or.inr (by linarith))
    · exact (rpow_pos_of_pos ((Nat.cast_pos.mpr (by simp)).trans hx.1) _).ne'

/--
lemma `continuousOn_termTSum` / 引理 `continuousOn_termTSum`

English:
lemma continuousOn_termTSum
  statement: ContinuousOn termTSum (Ici 1)
  proof: by
  -- We use dominated convergence, using `fun n ↦ term n 1` as our uniform bound (since `term` is
  -- monotone decreasing in `s`.)
  refine continuousOn_tsum (fun i => continuousOn_term _) term_tsum_one.summable (fun n s hs => ?_)
  rw [term]; rw [term]; rw [norm_of_nonneg]
  · simp_rw [intervalIntegral.integral_of_le (by linarith : (↑(n + 1) : Real) <= ↑(n + 1) + 1)]
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc (fun x hx => ?_)
    · exact (term_welldef n.succ_pos (zero_lt_one.trans_le hs)).1
    · exact (term_welldef n.succ_pos zero_lt_one).1
    · have : 1 <= x := le_trans (by simp) hx.1.le
      gcongr
      · exact sub_nonneg.mpr hx.1.le
      · exact hs
  · rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_nonneg measurableSet_Ioc (fun x hx => div_nonneg ?_ (rpow_nonneg ?_ _))
    all_goals linarith [hx.1]

@[deprecated (since := "2026-05-27")] alias continuousOn_term_tsum := continuousOn_termTSum

中文:
引理 continuousOn_termTSum
  结论: ContinuousOn termTSum (左闭右无界区间 1)
  证明: by
  -- We use dominated convergence, using `fun n ↦ term n 1` as our uniform bound (since `term` is
  -- monotone decreasing in `s`.)
  refine continuousOn_tsum (fun i => continuousOn_term _) term_tsum_one.summable (fun n s hs => ?_)
  rw [term]; rw [term]; rw [norm_of_nonneg]
  · simp_rw [intervalIntegral.integral_of_le (by linarith : (↑(n + 1) : Real) <= ↑(n + 1) + 1)]
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc (fun x hx => ?_)
    · exact (term_welldef n.succ_pos (zero_lt_one.trans_le hs)).1
    · exact (term_welldef n.succ_pos zero_lt_one).1
    · have : 1 <= x := le_trans (by simp) hx.1.le
      gcongr
      · exact sub_nonneg.mpr hx.1.le
      · exact hs
  · rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_nonneg measurableSet_Ioc (fun x hx => div_nonneg ?_ (rpow_nonneg ?_ _))
    all_goals linarith [hx.1]

@[deprecated (since := "2026-05-27")] alias continuousOn_term_tsum := continuousOn_termTSum
-/
lemma continuousOn_termTSum : ContinuousOn termTSum (Ici 1) := by
  -- We use dominated convergence, using `fun n ↦ term n 1` as our uniform bound (since `term` is
  -- monotone decreasing in `s`.)
  refine continuousOn_tsum (fun i => continuousOn_term _) term_tsum_one.summable (fun n s hs => ?_)
  rw [term]; rw [term]; rw [norm_of_nonneg]
  · simp_rw [intervalIntegral.integral_of_le (by linarith : (↑(n + 1) : Real) <= ↑(n + 1) + 1)]
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc (fun x hx => ?_)
    · exact (term_welldef n.succ_pos (zero_lt_one.trans_le hs)).1
    · exact (term_welldef n.succ_pos zero_lt_one).1
    · have : 1 <= x := le_trans (by simp) hx.1.le
      gcongr
      · exact sub_nonneg.mpr hx.1.le
      · exact hs
  · rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_nonneg measurableSet_Ioc (fun x hx => div_nonneg ?_ (rpow_nonneg ?_ _))
    all_goals linarith [hx.1]

@[deprecated (since := "2026-05-27")] alias continuousOn_term_tsum := continuousOn_termTSum

/--
lemma `tendsto_riemannZeta_sub_one_div_nhds_right` / 引理 `tendsto_riemannZeta_sub_one_div_nhds_right`

English:
lemma tendsto_riemannZeta_sub_one_div_nhds_right
  proof: by
  suffices Tendsto (fun s : Real => (∑' n : Nat, 1 / (n + 1 : Real) ^ s) - 1 / (s - 1))
    (𝓝[>] 1) (𝓝 γ) by
    apply ((Complex.continuous_ofReal.tendsto _).comp this).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Function.comp_apply, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_one, sub_left_inj, Complex.ofReal_tsum]
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
    congr 1 with n
    rw [Complex.ofReal_cpow (by positivity)]
    norm_cast
  suffices aux2 : Tendsto (fun s : Real => (∑' n : Nat, 1 / (n + 1 : Real) ^ s) - 1 / (s - 1))
    (𝓝[>] 1) (𝓝 (1 - termTSum 1)) by
    have := term_tsum_one.tsum_eq
    rw [← termTSum]; rw [eq_sub_iff_add_eq]; rw [← eq_sub_iff_add_eq'] at this
    simpa only [this] using aux2
  apply Tendsto.congr'
  · filter_upwards [self_mem_nhdsWithin] with s hs using (zeta_limit_aux1 hs).symm
  · apply tendsto_const_nhds.sub
    rw [← one_mul (termTSum 1)]
    apply (tendsto_id.mono_left nhdsWithin_le_nhds).mul
    have := continuousOn_termTSum.continuousWithinAt self_mem_Ici
    exact Tendsto.mono_left this (nhdsWithin_mono _ Ioi_subset_Ici_self)

中文:
引理 tendsto_riemannZeta_sub_one_div_nhds_right
  证明: by
  suffices Tendsto (fun s : Real => (∑' n : Nat, 1 / (n + 1 : Real) ^ s) - 1 / (s - 1))
    (𝓝[>] 1) (𝓝 γ) by
    apply ((Complex.continuous_ofReal.tendsto _).comp this).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Function.comp_apply, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_one, sub_left_inj, Complex.ofReal_tsum]
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
    congr 1 with n
    rw [Complex.ofReal_cpow (by positivity)]
    norm_cast
  suffices aux2 : Tendsto (fun s : Real => (∑' n : Nat, 1 / (n + 1 : Real) ^ s) - 1 / (s - 1))
    (𝓝[>] 1) (𝓝 (1 - termTSum 1)) by
    have := term_tsum_one.tsum_eq
    rw [← termTSum]; rw [eq_sub_iff_add_eq]; rw [← eq_sub_iff_add_eq'] at this
    simpa only [this] using aux2
  apply Tendsto.congr'
  · filter_upwards [self_mem_nhdsWithin] with s hs using (zeta_limit_aux1 hs).symm
  · apply tendsto_const_nhds.sub
    rw [← one_mul (termTSum 1)]
    apply (tendsto_id.mono_left nhdsWithin_le_nhds).mul
    have := continuousOn_termTSum.continuousWithinAt self_mem_Ici
    exact Tendsto.mono_left this (nhdsWithin_mono _ Ioi_subset_Ici_self)

Depends on / 依赖: Complex.continuous_ofReal.tendsto, Complex.ofReal_cpow, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_sub, Complex.ofReal_tsum, Function, Function.comp_apply, Tendsto, comp_apply, continuous_ofReal, filter_upwards, ofReal_cpow, ofReal_div, ofReal_one, ofReal_sub, ofReal_tsum, self_mem_nhdsWithin, sub_left_inj, tendsto
-/
lemma tendsto_riemannZeta_sub_one_div_nhds_right :
    Tendsto (fun s : Real => riemannZeta s - 1 / (s - 1)) (𝓝[>] 1) (𝓝 γ) := by
  suffices Tendsto (fun s : Real => (∑' n : Nat, 1 / (n + 1 : Real) ^ s) - 1 / (s - 1))
    (𝓝[>] 1) (𝓝 γ) by
    apply ((Complex.continuous_ofReal.tendsto _).comp this).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Function.comp_apply, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_one, sub_left_inj, Complex.ofReal_tsum]
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
    congr 1 with n
    rw [Complex.ofReal_cpow (by positivity)]
    norm_cast
  suffices aux2 : Tendsto (fun s : Real => (∑' n : Nat, 1 / (n + 1 : Real) ^ s) - 1 / (s - 1))
    (𝓝[>] 1) (𝓝 (1 - termTSum 1)) by
    have := term_tsum_one.tsum_eq
    rw [← termTSum]; rw [eq_sub_iff_add_eq]; rw [← eq_sub_iff_add_eq'] at this
    simpa only [this] using aux2
  apply Tendsto.congr'
  · filter_upwards [self_mem_nhdsWithin] with s hs using (zeta_limit_aux1 hs).symm
  · apply tendsto_const_nhds.sub
    rw [← one_mul (termTSum 1)]
    apply (tendsto_id.mono_left nhdsWithin_le_nhds).mul
    have := continuousOn_termTSum.continuousWithinAt self_mem_Ici
    exact Tendsto.mono_left this (nhdsWithin_mono _ Ioi_subset_Ici_self)

/--
theorem `_root_.tendsto_riemannZeta_sub_one_div` / 定理 `_root_.tendsto_riemannZeta_sub_one_div`

English:
theorem _root_.tendsto_riemannZeta_sub_one_div
  proof: by
  -- We use the removable-singularity theorem to show that *some* limit over `𝓝[≠] (1 : ℂ)` exists,
  -- and then use the previous result to deduce that this limit must be `γ`.
  let f (s : Complex) := riemannZeta s - 1 / (s - 1)
  suffices exists C, Tendsto f (𝓝[!=] 1) (𝓝 C) by
    obtain ⟨C, hC⟩ := this
    suffices Tendsto (fun s : Real => f s) _ _
      from (tendsto_nhds_unique this tendsto_riemannZeta_sub_one_div_nhds_right) ▸ hC
    refine hC.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds ..)
    · filter_upwards [self_mem_nhdsWithin] with a ha
      rw [mem_compl_singleton_iff]; rw [← Complex.ofReal_one]; rw [Ne]; rw [Complex.ofReal_inj]
      exact ne_of_gt ha
  refine ⟨_, Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO ?_ ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with s hs
    refine (differentiableAt_riemannZeta hs).sub ((differentiableAt_const _).div ?_ ?_)
    · fun_prop
    · rwa [mem_compl_singleton_iff, ← sub_ne_zero] at hs
  · refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht ht'
      rw [inv_eq_zero]; rw [sub_eq_zero] at ht'
      tauto
    · simp_rw [div_eq_mul_inv, inv_inv, sub_mul,
        (by ring_nf : 𝓝 (0 : Complex) = 𝓝 ((1 - 1) - f 1 * (1 - 1)))]
      apply Tendsto.sub
      · simp_rw [mul_comm (f _), f, mul_sub]
        apply riemannZeta_residue_one.sub
        refine Tendsto.congr' ?_ (tendsto_const_nhds.mono_left nhdsWithin_le_nhds)
        filter_upwards [self_mem_nhdsWithin] with x hx
        field [sub_ne_zero.mpr <| mem_compl_singleton_iff.mp hx]
      · exact ((tendsto_id.sub tendsto_const_nhds).mono_left nhdsWithin_le_nhds).const_mul _

中文:
定理 _root_.tendsto_riemannZeta_sub_one_div
  证明: by
  -- We use the removable-singularity theorem to show that *some* limit over `𝓝[≠] (1 : ℂ)` exists,
  -- and then use the previous result to deduce that this limit must be `γ`.
  let f (s : Complex) := riemannZeta s - 1 / (s - 1)
  suffices exists C, Tendsto f (𝓝[!=] 1) (𝓝 C) by
    obtain ⟨C, hC⟩ := this
    suffices Tendsto (fun s : Real => f s) _ _
      from (tendsto_nhds_unique this tendsto_riemannZeta_sub_one_div_nhds_right) ▸ hC
    refine hC.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds ..)
    · filter_upwards [self_mem_nhdsWithin] with a ha
      rw [mem_compl_singleton_iff]; rw [← Complex.ofReal_one]; rw [Ne]; rw [Complex.ofReal_inj]
      exact ne_of_gt ha
  refine ⟨_, Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO ?_ ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with s hs
    refine (differentiableAt_riemannZeta hs).sub ((differentiableAt_const _).div ?_ ?_)
    · fun_prop
    · rwa [mem_compl_singleton_iff, ← sub_ne_zero] at hs
  · refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht ht'
      rw [inv_eq_zero]; rw [sub_eq_zero] at ht'
      tauto
    · simp_rw [div_eq_mul_inv, inv_inv, sub_mul,
        (by ring_nf : 𝓝 (0 : Complex) = 𝓝 ((1 - 1) - f 1 * (1 - 1)))]
      apply Tendsto.sub
      · simp_rw [mul_comm (f _), f, mul_sub]
        apply riemannZeta_residue_one.sub
        refine Tendsto.congr' ?_ (tendsto_const_nhds.mono_left nhdsWithin_le_nhds)
        filter_upwards [self_mem_nhdsWithin] with x hx
        field [sub_ne_zero.mpr <| mem_compl_singleton_iff.mp hx]
      · exact ((tendsto_id.sub tendsto_const_nhds).mono_left nhdsWithin_le_nhds).const_mul _
-/
theorem _root_.tendsto_riemannZeta_sub_one_div :
    Tendsto (fun s : Complex => riemannZeta s - 1 / (s - 1)) (𝓝[!=] 1) (𝓝 γ) := by
  -- We use the removable-singularity theorem to show that *some* limit over `𝓝[≠] (1 : ℂ)` exists,
  -- and then use the previous result to deduce that this limit must be `γ`.
  let f (s : Complex) := riemannZeta s - 1 / (s - 1)
  suffices exists C, Tendsto f (𝓝[!=] 1) (𝓝 C) by
    obtain ⟨C, hC⟩ := this
    suffices Tendsto (fun s : Real => f s) _ _
      from (tendsto_nhds_unique this tendsto_riemannZeta_sub_one_div_nhds_right) ▸ hC
    refine hC.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds ..)
    · filter_upwards [self_mem_nhdsWithin] with a ha
      rw [mem_compl_singleton_iff]; rw [← Complex.ofReal_one]; rw [Ne]; rw [Complex.ofReal_inj]
      exact ne_of_gt ha
  refine ⟨_, Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO ?_ ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with s hs
    refine (differentiableAt_riemannZeta hs).sub ((differentiableAt_const _).div ?_ ?_)
    · fun_prop
    · rwa [mem_compl_singleton_iff, ← sub_ne_zero] at hs
  · refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht ht'
      rw [inv_eq_zero]; rw [sub_eq_zero] at ht'
      tauto
    · simp_rw [div_eq_mul_inv, inv_inv, sub_mul,
        (by ring_nf : 𝓝 (0 : Complex) = 𝓝 ((1 - 1) - f 1 * (1 - 1)))]
      apply Tendsto.sub
      · simp_rw [mul_comm (f _), f, mul_sub]
        apply riemannZeta_residue_one.sub
        refine Tendsto.congr' ?_ (tendsto_const_nhds.mono_left nhdsWithin_le_nhds)
        filter_upwards [self_mem_nhdsWithin] with x hx
        field [sub_ne_zero.mpr <| mem_compl_singleton_iff.mp hx]
      · exact ((tendsto_id.sub tendsto_const_nhds).mono_left nhdsWithin_le_nhds).const_mul _

/--
lemma `_root_.isBigO_riemannZeta_sub_one_div` / 引理 `_root_.isBigO_riemannZeta_sub_one_div`

English:
lemma _root_.isBigO_riemannZeta_sub_one_div
  given: {F : Type*} [Norm F] [One F] [NormOneClass F]
  proof: by
  simpa only [Asymptotics.isBigO_one_nhds_ne_iff] using
     tendsto_riemannZeta_sub_one_div.isBigO_one (F := F)

中文:
引理 _root_.isBigO_riemannZeta_sub_one_div
  条件: {F : 类型} [范数 F] [幺 F] [NormOne类 F]
  证明: by
  simpa only [Asymptotics.isBigO_one_nhds_ne_iff] using
     tendsto_riemannZeta_sub_one_div.isBigO_one (F := F)

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_one_nhds_ne_iff, isBigO_one, isBigO_one_nhds_ne_iff, tendsto_riemannZeta_sub_one_div, tendsto_riemannZeta_sub_one_div.isBigO_one
-/
lemma _root_.isBigO_riemannZeta_sub_one_div {F : Type*} [Norm F] [One F] [NormOneClass F] :
    (fun s : Complex => riemannZeta s - 1 / (s - 1)) =O[𝓝 1] (fun _ => 1 : Complex -> F) := by
  simpa only [Asymptotics.isBigO_one_nhds_ne_iff] using
     tendsto_riemannZeta_sub_one_div.isBigO_one (F := F)

end continuity

section val_at_one

open Complex

/--
lemma `tendsto_Gamma_term_aux` / 引理 `tendsto_Gamma_term_aux`

English:
lemma tendsto_Gamma_term_aux
  statement: Tendsto (fun s => 1 / (s - 1) - 1 / GammaReal s / (s - 1)) (𝓝[!=] 1)
  proof: by
  have h := hasDerivAt_GammaReal_one
  rw [hasDerivAt_iff_tendsto_slope]; rw [slope_fun_def_field]; rw [GammaReal_one] at h
  have := h.div (hasDerivAt_GammaReal_one.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (GammaReal_one.trans_ne one_ne_zero)
  rw [GammaReal_one]; rw [div_one] at this
  refine this.congr' ?_
  have : {z | 0 < re z} in 𝓝 (1 : Complex) := by
    apply (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
    simp only [mem_preimage, one_re, mem_Ioi, zero_lt_one]
  rw [EventuallyEq]; rw [eventually_nhdsWithin_iff]
  filter_upwards [this] with a ha _
  rw [Pi.div_apply]; rw [← sub_div]; rw [div_right_comm]; rw [sub_div' (GammaReal_ne_zero_of_re_pos ha)]; rw [one_mul]

中文:
引理 tendsto_Gamma_term_aux
  结论: 收敛 (fun s => 1 / (s - 1) - 1 / Gamma实数 s / (s - 1)) (𝓝[!=] 1)
  证明: by
  have h := hasDerivAt_GammaReal_one
  rw [hasDerivAt_iff_tendsto_slope]; rw [slope_fun_def_field]; rw [GammaReal_one] at h
  have := h.div (hasDerivAt_GammaReal_one.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (GammaReal_one.trans_ne one_ne_zero)
  rw [GammaReal_one]; rw [div_one] at this
  refine this.congr' ?_
  have : {z | 0 < re z} in 𝓝 (1 : Complex) := by
    apply (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
    simp only [mem_preimage, one_re, mem_Ioi, zero_lt_one]
  rw [EventuallyEq]; rw [eventually_nhdsWithin_iff]
  filter_upwards [this] with a ha _
  rw [Pi.div_apply]; rw [← sub_div]; rw [div_right_comm]; rw [sub_div' (GammaReal_ne_zero_of_re_pos ha)]; rw [one_mul]

Depends on / 依赖: EventuallyEq, GammaReal_one, GammaReal_one.trans_ne, continuousAt, continuous_re, continuous_re.isOpen_preimage, div_one, h.div, hasDerivAt_GammaReal_one, hasDerivAt_GammaReal_one.continuousAt.tendsto.mono_left, hasDerivAt_iff_tendsto_slope, isOpen_Ioi, isOpen_preimage, mem_Ioi, mem_nhds, mem_preimage, mono_left, nhdsWithin_le_nhds, one_ne_zero, one_re
-/
lemma tendsto_Gamma_term_aux : Tendsto (fun s => 1 / (s - 1) - 1 / GammaReal s / (s - 1)) (𝓝[!=] 1)
    (𝓝 (-(γ + Complex.log (4 * ↑π)) / 2)) := by
  have h := hasDerivAt_GammaReal_one
  rw [hasDerivAt_iff_tendsto_slope]; rw [slope_fun_def_field]; rw [GammaReal_one] at h
  have := h.div (hasDerivAt_GammaReal_one.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (GammaReal_one.trans_ne one_ne_zero)
  rw [GammaReal_one]; rw [div_one] at this
  refine this.congr' ?_
  have : {z | 0 < re z} in 𝓝 (1 : Complex) := by
    apply (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
    simp only [mem_preimage, one_re, mem_Ioi, zero_lt_one]
  rw [EventuallyEq]; rw [eventually_nhdsWithin_iff]
  filter_upwards [this] with a ha _
  rw [Pi.div_apply]; rw [← sub_div]; rw [div_right_comm]; rw [sub_div' (GammaReal_ne_zero_of_re_pos ha)]; rw [one_mul]

/--
lemma `tendsto_riemannZeta_sub_one_div_GammaReal` / 引理 `tendsto_riemannZeta_sub_one_div_GammaReal`

English:
lemma tendsto_riemannZeta_sub_one_div_GammaReal
  proof: by
  have := tendsto_riemannZeta_sub_one_div.add tendsto_Gamma_term_aux
  simp_rw [sub_add_sub_cancel] at this
  convert! this using 2
  ring_nf

中文:
引理 tendsto_riemannZeta_sub_one_div_Gamma实数
  证明: by
  have := tendsto_riemannZeta_sub_one_div.add tendsto_Gamma_term_aux
  simp_rw [sub_add_sub_cancel] at this
  convert! this using 2
  ring_nf

Depends on / 依赖: convert, ring_nf, simp_rw, sub_add_sub_cancel, tendsto_Gamma_term_aux, tendsto_riemannZeta_sub_one_div, tendsto_riemannZeta_sub_one_div.add
-/
lemma tendsto_riemannZeta_sub_one_div_GammaReal :
    Tendsto (fun s => riemannZeta s - 1 / GammaReal s / (s - 1)) (𝓝[!=] 1)
    (𝓝 ((γ - Complex.log (4 * ↑π)) / 2)) := by
  have := tendsto_riemannZeta_sub_one_div.add tendsto_Gamma_term_aux
  simp_rw [sub_add_sub_cancel] at this
  convert! this using 2
  ring_nf

end val_at_one

end ZetaAsymptotics

open scoped Real
open Complex ComplexConjugate

/--
lemma `riemannZeta_one` / 引理 `riemannZeta_one`

English:
lemma riemannZeta_one
  statement: riemannZeta 1 = (γ - log (4 * π)) / 2
  proof: by
  have := (HurwitzZeta.tendsto_hurwitzZetaEven_sub_one_div_nhds_one 0).mono_left
 nhdsWithin_le_nhds (s := {1}ᶜ)
  simp only [HurwitzZeta.hurwitzZetaEven_zero, div_right_comm _ _ (GammaReal _)] at this
  exact tendsto_nhds_unique this ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_GammaReal

中文:
引理 riemannZeta_one
  结论: riemannZeta 1 = (γ - log (4 * π)) / 2
  证明: by
  have := (HurwitzZeta.tendsto_hurwitzZetaEven_sub_one_div_nhds_one 0).mono_left
 nhdsWithin_le_nhds (s := {1}ᶜ)
  simp only [HurwitzZeta.hurwitzZetaEven_zero, div_right_comm _ _ (GammaReal _)] at this
  exact tendsto_nhds_unique this ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_GammaReal

Depends on / 依赖: GammaReal, HurwitzZeta, HurwitzZeta.hurwitzZetaEven_zero, HurwitzZeta.tendsto_hurwitzZetaEven_sub_one_div_nhds_one, ZetaAsymptotics, ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_GammaReal, div_right_comm, hurwitzZetaEven_zero, mono_left, nhdsWithin_le_nhds, tendsto_hurwitzZetaEven_sub_one_div_nhds_one, tendsto_nhds_unique, tendsto_riemannZeta_sub_one_div_GammaReal
-/
lemma riemannZeta_one : riemannZeta 1 = (γ - log (4 * π)) / 2 := by
  have := (HurwitzZeta.tendsto_hurwitzZetaEven_sub_one_div_nhds_one 0).mono_left
 nhdsWithin_le_nhds (s := {1}ᶜ)
  simp only [HurwitzZeta.hurwitzZetaEven_zero, div_right_comm _ _ (GammaReal _)] at this
  exact tendsto_nhds_unique this ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_GammaReal

/--
lemma `completedRiemannZeta_one` / 引理 `completedRiemannZeta_one`

English:
lemma completedRiemannZeta_one
  statement: completedRiemannZeta 1 = (γ - log (4 * π)) / 2
  proof: (riemannZeta_one ▸ div_one (_ : Complex) ▸ GammaReal_one ▸ riemannZeta_def_of_ne_zero one_ne_zero).symm

中文:
引理 completedRiemannZeta_one
  结论: completedRiemannZeta 1 = (γ - log (4 * π)) / 2
  证明: (riemannZeta_one ▸ div_one (_ : Complex) ▸ GammaReal_one ▸ riemannZeta_def_of_ne_zero one_ne_zero).symm

Depends on / 依赖: GammaReal_one, div_one, one_ne_zero, riemannZeta_def_of_ne_zero, riemannZeta_one
-/
lemma completedRiemannZeta_one : completedRiemannZeta 1 = (γ - log (4 * π)) / 2 :=
  (riemannZeta_one ▸ div_one (_ : Complex) ▸ GammaReal_one ▸ riemannZeta_def_of_ne_zero one_ne_zero).symm

/--
lemma `completedRiemannZeta₀_one` / 引理 `completedRiemannZeta₀_one`

English:
lemma completedRiemannZeta₀_one
  statement: completedRiemannZeta₀ 1 = (γ - log (4 * ↑π)) / 2 + 1
  proof: by
  have := completedRiemannZeta_eq 1
  rw [sub_self]; rw [div_zero]; rw [div_one]; rw [sub_zero]; rw [eq_sub_iff_add_eq] at this
  rw [← this]; rw [completedRiemannZeta_one]

中文:
引理 completedRiemannZeta₀_one
  结论: completedRiemannZeta₀ 1 = (γ - log (4 * ↑π)) / 2 + 1
  证明: by
  have := completedRiemannZeta_eq 1
  rw [sub_self]; rw [div_zero]; rw [div_one]; rw [sub_zero]; rw [eq_sub_iff_add_eq] at this
  rw [← this]; rw [completedRiemannZeta_one]

Depends on / 依赖: completedRiemannZeta_eq, completedRiemannZeta_one, div_one, div_zero, eq_sub_iff_add_eq, sub_self, sub_zero
-/
lemma completedRiemannZeta₀_one : completedRiemannZeta₀ 1 = (γ - log (4 * ↑π)) / 2 + 1 := by
  have := completedRiemannZeta_eq 1
  rw [sub_self]; rw [div_zero]; rw [div_one]; rw [sub_zero]; rw [eq_sub_iff_add_eq] at this
  rw [← this]; rw [completedRiemannZeta_one]

/--
lemma `riemannZeta_one_ne_zero` / 引理 `riemannZeta_one_ne_zero`

English:
lemma riemannZeta_one_ne_zero
  statement: riemannZeta 1 != 0
  proof: by
  -- This one's for you, Kevin.
  suffices (γ - Real.log (4 * π)) / 2 != 0 by
    simpa only [riemannZeta_one, ← ofReal_ne_zero, ofReal_log (by positivity : 0 <= 4 * π),
      push_cast]
  refine div_ne_zero (sub_lt_zero.mpr (lt_trans ?_ ?_ (b := 1))).ne two_ne_zero
  · exact Real.eulerMascheroniConstant_lt_two_thirds.trans (by norm_num)
  · rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact (lt_trans Real.exp_one_lt_d9 (by norm_num)).trans_le
 mul_le_mul_of_nonneg_left Real.two_le_pi (by simp)

中文:
引理 riemannZeta_one_ne_zero
  结论: riemannZeta 1 != 0
  证明: by
  -- This one's for you, Kevin.
  suffices (γ - Real.log (4 * π)) / 2 != 0 by
    simpa only [riemannZeta_one, ← ofReal_ne_zero, ofReal_log (by positivity : 0 <= 4 * π),
      push_cast]
  refine div_ne_zero (sub_lt_zero.mpr (lt_trans ?_ ?_ (b := 1))).ne two_ne_zero
  · exact Real.eulerMascheroniConstant_lt_two_thirds.trans (by norm_num)
  · rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact (lt_trans Real.exp_one_lt_d9 (by norm_num)).trans_le
 mul_le_mul_of_nonneg_left Real.two_le_pi (by simp)
-/
lemma riemannZeta_one_ne_zero : riemannZeta 1 != 0 := by
  -- This one's for you, Kevin.
  suffices (γ - Real.log (4 * π)) / 2 != 0 by
    simpa only [riemannZeta_one, ← ofReal_ne_zero, ofReal_log (by positivity : 0 <= 4 * π),
      push_cast]
  refine div_ne_zero (sub_lt_zero.mpr (lt_trans ?_ ?_ (b := 1))).ne two_ne_zero
  · exact Real.eulerMascheroniConstant_lt_two_thirds.trans (by norm_num)
  · rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact (lt_trans Real.exp_one_lt_d9 (by norm_num)).trans_le
 mul_le_mul_of_nonneg_left Real.two_le_pi (by simp)

/-- **Conjugation symmetry of the Riemann zeta function**: `ζ (conj s) = conj (ζ s)`.

Since `ζ` has real Dirichlet coefficients, `conj (ζ (conj z)) = ζ z` holds termwise for
`1 < re z`, and the identity principle propagates this to all `s ≠ 1`; the junk value `ζ 1` is
real, so the identity also holds at `s = 1`. -/
@[simp]
/--
theorem `riemannZeta_conj` / 定理 `riemannZeta_conj`

English:
theorem riemannZeta_conj
  given: (s : Complex)
  statement: riemannZeta (conj s) = conj (riemannZeta s)
  proof: by
  rcases eq_or_ne s 1 with rfl | hs
  · have h : riemannZeta 1 = ((γ - Real.log (4 * π)) / 2 : Real) := by
      rw [riemannZeta_one]; rw [ofReal_div]; rw [ofReal_sub]; rw [ofReal_log (by positivity : (0 : Real) <= 4 * π)]
      norm_cast
    rw [map_one]; rw [h]; rw [conj_ofReal]
  · -- `conj ∘ ζ ∘ conj` is analytic on `{1}ᶜ` and agrees with `ζ` termwise on `1 < re z`, so
    -- the identity principle propagates the equality to the connected set `{1}ᶜ`.
    have hg_an : AnalyticOnNhd Complex (fun z => conj (riemannZeta (conj z))) {1}ᶜ :=
      DifferentiableOn.analyticOnNhd
        (fun z hz => (differentiableAt_conj_conj_iff.mpr <| differentiableAt_riemannZeta <|
          (map_ne_one_iff _ (starRingEnd Complex).injective).mpr hz).differentiableWithinAt)
        isOpen_compl_singleton
    have hgz (z : Complex) (hz : 1 < z.re) : conj (riemannZeta (conj z)) = riemannZeta z := by
      rw [zeta_eq_tsum_one_div_nat_cpow (by rwa [conj_re]), conj_tsum,
        zeta_eq_tsum_one_div_nat_cpow hz]
      exact tsum_congr fun n => by
        rw [map_div₀]; rw [map_one]; rw [← conj_cpow _ _ (by rw [natCast_arg]; positivity), conj_natCast]
    have heq : EqOn (fun z => conj (riemannZeta (conj z))) riemannZeta {1}ᶜ :=
      hg_an.eqOn_of_preconnected_of_eventuallyEq analyticOn_riemannZeta
        (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
        (by norm_num : (2 : Complex) in _)
        (eventuallyEq_of_mem
          ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)) hgz)
    simpa using congrArg (starRingEnd Complex) (heq hs)

中文:
定理 riemannZeta_conj
  条件: (s : 复形)
  结论: riemannZeta (conj s) = conj (riemannZeta s)
  证明: by
  rcases eq_or_ne s 1 with rfl | hs
  · have h : riemannZeta 1 = ((γ - Real.log (4 * π)) / 2 : Real) := by
      rw [riemannZeta_one]; rw [ofReal_div]; rw [ofReal_sub]; rw [ofReal_log (by positivity : (0 : Real) <= 4 * π)]
      norm_cast
    rw [map_one]; rw [h]; rw [conj_ofReal]
  · -- `conj ∘ ζ ∘ conj` is analytic on `{1}ᶜ` and agrees with `ζ` termwise on `1 < re z`, so
    -- the identity principle propagates the equality to the connected set `{1}ᶜ`.
    have hg_an : AnalyticOnNhd Complex (fun z => conj (riemannZeta (conj z))) {1}ᶜ :=
      DifferentiableOn.analyticOnNhd
        (fun z hz => (differentiableAt_conj_conj_iff.mpr <| differentiableAt_riemannZeta <|
          (map_ne_one_iff _ (starRingEnd Complex).injective).mpr hz).differentiableWithinAt)
        isOpen_compl_singleton
    have hgz (z : Complex) (hz : 1 < z.re) : conj (riemannZeta (conj z)) = riemannZeta z := by
      rw [zeta_eq_tsum_one_div_nat_cpow (by rwa [conj_re]), conj_tsum,
        zeta_eq_tsum_one_div_nat_cpow hz]
      exact tsum_congr fun n => by
        rw [map_div₀]; rw [map_one]; rw [← conj_cpow _ _ (by rw [natCast_arg]; positivity), conj_natCast]
    have heq : EqOn (fun z => conj (riemannZeta (conj z))) riemannZeta {1}ᶜ :=
      hg_an.eqOn_of_preconnected_of_eventuallyEq analyticOn_riemannZeta
        (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
        (by norm_num : (2 : Complex) in _)
        (eventuallyEq_of_mem
          ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)) hgz)
    simpa using congrArg (starRingEnd Complex) (heq hs)

Depends on / 依赖: Real.log, agrees, analytic, conj_ofReal, eq_or_ne, map_one, ofReal_div, ofReal_log, ofReal_sub, riemannZeta, riemannZeta_one, termwise
-/
theorem riemannZeta_conj (s : Complex) : riemannZeta (conj s) = conj (riemannZeta s) := by
  rcases eq_or_ne s 1 with rfl | hs
  · have h : riemannZeta 1 = ((γ - Real.log (4 * π)) / 2 : Real) := by
      rw [riemannZeta_one]; rw [ofReal_div]; rw [ofReal_sub]; rw [ofReal_log (by positivity : (0 : Real) <= 4 * π)]
      norm_cast
    rw [map_one]; rw [h]; rw [conj_ofReal]
  · -- `conj ∘ ζ ∘ conj` is analytic on `{1}ᶜ` and agrees with `ζ` termwise on `1 < re z`, so
    -- the identity principle propagates the equality to the connected set `{1}ᶜ`.
    have hg_an : AnalyticOnNhd Complex (fun z => conj (riemannZeta (conj z))) {1}ᶜ :=
      DifferentiableOn.analyticOnNhd
        (fun z hz => (differentiableAt_conj_conj_iff.mpr <| differentiableAt_riemannZeta <|
          (map_ne_one_iff _ (starRingEnd Complex).injective).mpr hz).differentiableWithinAt)
        isOpen_compl_singleton
    have hgz (z : Complex) (hz : 1 < z.re) : conj (riemannZeta (conj z)) = riemannZeta z := by
      rw [zeta_eq_tsum_one_div_nat_cpow (by rwa [conj_re]), conj_tsum,
        zeta_eq_tsum_one_div_nat_cpow hz]
      exact tsum_congr fun n => by
        rw [map_div₀]; rw [map_one]; rw [← conj_cpow _ _ (by rw [natCast_arg]; positivity), conj_natCast]
    have heq : EqOn (fun z => conj (riemannZeta (conj z))) riemannZeta {1}ᶜ :=
      hg_an.eqOn_of_preconnected_of_eventuallyEq analyticOn_riemannZeta
        (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
        (by norm_num : (2 : Complex) in _)
        (eventuallyEq_of_mem
          ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)) hgz)
    simpa using congrArg (starRingEnd Complex) (heq hs)

/--
lemma `riemannZeta_eventually_ne_zero_nhds_one` / 引理 `riemannZeta_eventually_ne_zero_nhds_one`

English:
lemma riemannZeta_eventually_ne_zero_nhds_one
  statement: forallᶠ s in 𝓝 1, riemannZeta s != 0
  proof: by
  filter_upwards [eventually_nhdsWithin_iff.1 <| riemannZeta_residue_one.eventually_ne one_ne_zero]
  grind [riemannZeta_one_ne_zero]

中文:
引理 riemannZeta_eventually_ne_zero_nhds_one
  结论: 对任意ᶠ s in 𝓝 1, riemannZeta s != 0
  证明: by
  filter_upwards [eventually_nhdsWithin_iff.1 <| riemannZeta_residue_one.eventually_ne one_ne_zero]
  grind [riemannZeta_one_ne_zero]

Depends on / 依赖: eventually_ne, eventually_nhdsWithin_iff, filter_upwards, one_ne_zero, riemannZeta_one_ne_zero, riemannZeta_residue_one, riemannZeta_residue_one.eventually_ne
-/
lemma riemannZeta_eventually_ne_zero_nhds_one : forallᶠ s in 𝓝 1, riemannZeta s != 0 := by
  filter_upwards [eventually_nhdsWithin_iff.1 <| riemannZeta_residue_one.eventually_ne one_ne_zero]
  grind [riemannZeta_one_ne_zero]

/--
lemma `completedRiemannZeta₀_zero` / 引理 `completedRiemannZeta₀_zero`

English:
lemma completedRiemannZeta₀_zero
  statement: completedRiemannZeta₀ 0 = (γ - Complex.log (4 * π)) / 2 + 1
  proof: by
  rw [← completedRiemannZeta₀_one_sub]
  simp [completedRiemannZeta₀_one]

中文:
引理 completedRiemannZeta₀_zero
  结论: completedRiemannZeta₀ 0 = (γ - 复形.log (4 * π)) / 2 + 1
  证明: by
  rw [← completedRiemannZeta₀_one_sub]
  simp [completedRiemannZeta₀_one]
-/
lemma completedRiemannZeta₀_zero : completedRiemannZeta₀ 0 = (γ - Complex.log (4 * π)) / 2 + 1 := by
  rw [← completedRiemannZeta₀_one_sub]
  simp [completedRiemannZeta₀_one]

/--
theorem `deriv_riemannZeta_zero` / 定理 `deriv_riemannZeta_zero`

English:
theorem deriv_riemannZeta_zero
  proof: by
  rw [funext riemannZeta_eq_mul_completedRiemannZeta₀]
  apply HasDerivAt.deriv
  have h₁ : HasDerivAt ((id * completedRiemannZeta₀ - 1) - id / (1 - id)) _ 0 :=
    .sub
      (.sub (.mul (hasDerivAt_id 0) differentiable_completedZeta₀.differentiableAt.hasDerivAt)
        (hasDerivAt_const 0 1))
      (.div (hasDerivAt_id 0) (.sub (hasDerivAt_const 0 1) (hasDerivAt_id 0)) (by simp))
  have h₂ : HasDerivAt ((fun x : Complex => 2) * fun (x : Complex) => (π : Complex) ^ (-x / 2)) _ 0 :=
.mul (hasDerivAt_const 0 2)
    .cpow (hasDerivAt_const 0 _) (.div_const (.neg <| hasDerivAt_id 0) 2) (by simp [Real.pi_pos])
  have h₃ : HasDerivAt (Gamma ∘ fun x => x / 2 + 1) (deriv Gamma (0 / 2 + 1) * (1 / 2 + 0)) 0 := by
    refine (differentiableAt_Gamma _ ?_).hasDerivAt.comp 0 ?_
    · simp only [zero_div]
      norm_cast
      simp
    · exact ((hasDerivAt_id 0).div_const 2).add (hasDerivAt_const 0 1)
  suffices h : -(log (2 * π) * 2) = γ - log (2 * 2 * π) + (-log π + -γ) by
    norm_num only at h
    convert! h₁.mul ((h₂.mul h₃).inv (by simp)) using 1
    simpa [completedRiemannZeta₀_zero, hasDerivAt_Gamma_one.deriv, field]
  open ComplexOrder in
  repeat rw [log_mul (by positivity) (by positivity) (by simp [arg, LT.lt.le, Real.pi_pos])]
  ring

中文:
定理 deriv_riemannZeta_zero
  证明: by
  rw [funext riemannZeta_eq_mul_completedRiemannZeta₀]
  apply HasDerivAt.deriv
  have h₁ : HasDerivAt ((id * completedRiemannZeta₀ - 1) - id / (1 - id)) _ 0 :=
    .sub
      (.sub (.mul (hasDerivAt_id 0) differentiable_completedZeta₀.differentiableAt.hasDerivAt)
        (hasDerivAt_const 0 1))
      (.div (hasDerivAt_id 0) (.sub (hasDerivAt_const 0 1) (hasDerivAt_id 0)) (by simp))
  have h₂ : HasDerivAt ((fun x : Complex => 2) * fun (x : Complex) => (π : Complex) ^ (-x / 2)) _ 0 :=
.mul (hasDerivAt_const 0 2)
    .cpow (hasDerivAt_const 0 _) (.div_const (.neg <| hasDerivAt_id 0) 2) (by simp [Real.pi_pos])
  have h₃ : HasDerivAt (Gamma ∘ fun x => x / 2 + 1) (deriv Gamma (0 / 2 + 1) * (1 / 2 + 0)) 0 := by
    refine (differentiableAt_Gamma _ ?_).hasDerivAt.comp 0 ?_
    · simp only [zero_div]
      norm_cast
      simp
    · exact ((hasDerivAt_id 0).div_const 2).add (hasDerivAt_const 0 1)
  suffices h : -(log (2 * π) * 2) = γ - log (2 * 2 * π) + (-log π + -γ) by
    norm_num only at h
    convert! h₁.mul ((h₂.mul h₃).inv (by simp)) using 1
    simpa [completedRiemannZeta₀_zero, hasDerivAt_Gamma_one.deriv, field]
  open ComplexOrder in
  repeat rw [log_mul (by positivity) (by positivity) (by simp [arg, LT.lt.le, Real.pi_pos])]
  ring

Depends on / 依赖: HasDerivAt, HasDerivAt.deriv, differentiableAt, differentiableAt.hasDerivAt, hasDerivAt, hasDerivAt_const, hasDerivAt_id
-/
theorem deriv_riemannZeta_zero :
    deriv riemannZeta 0 = -log (2 * π) / 2 := by
  rw [funext riemannZeta_eq_mul_completedRiemannZeta₀]
  apply HasDerivAt.deriv
  have h₁ : HasDerivAt ((id * completedRiemannZeta₀ - 1) - id / (1 - id)) _ 0 :=
    .sub
      (.sub (.mul (hasDerivAt_id 0) differentiable_completedZeta₀.differentiableAt.hasDerivAt)
        (hasDerivAt_const 0 1))
      (.div (hasDerivAt_id 0) (.sub (hasDerivAt_const 0 1) (hasDerivAt_id 0)) (by simp))
  have h₂ : HasDerivAt ((fun x : Complex => 2) * fun (x : Complex) => (π : Complex) ^ (-x / 2)) _ 0 :=
.mul (hasDerivAt_const 0 2)
    .cpow (hasDerivAt_const 0 _) (.div_const (.neg <| hasDerivAt_id 0) 2) (by simp [Real.pi_pos])
  have h₃ : HasDerivAt (Gamma ∘ fun x => x / 2 + 1) (deriv Gamma (0 / 2 + 1) * (1 / 2 + 0)) 0 := by
    refine (differentiableAt_Gamma _ ?_).hasDerivAt.comp 0 ?_
    · simp only [zero_div]
      norm_cast
      simp
    · exact ((hasDerivAt_id 0).div_const 2).add (hasDerivAt_const 0 1)
  suffices h : -(log (2 * π) * 2) = γ - log (2 * 2 * π) + (-log π + -γ) by
    norm_num only at h
    convert! h₁.mul ((h₂.mul h₃).inv (by simp)) using 1
    simpa [completedRiemannZeta₀_zero, hasDerivAt_Gamma_one.deriv, field]
  open ComplexOrder in
  repeat rw [log_mul (by positivity) (by positivity) (by simp [arg, LT.lt.le, Real.pi_pos])]
  ring

section near_one

/-!
## More asymptotics near `s = 1`

To facilitate the analysis of `riemannZeta` near `s = 1`, we write `riemannZeta s` additively as
`(s-1)⁻¹ + riemannZeta₀ s` and multiplicatively as `(s-1)⁻¹ * riemannZeta₁ s` for certain
entire functions `riemannZeta₀`, `riemannZeta₁`.
-/

open Asymptotics

/--
Definition of `riemannZeta₀` / `riemannZeta₀` 的定义

English:
definition riemannZeta₀
  signature: (s : Complex)
  body: if s = 1 then γ else riemannZeta s - (s-1)⁻¹

中文:
定义 riemannZeta₀
  签名: (s : 复形)
  定义体: if s = 1 then γ else riemannZeta s - (s-1)⁻¹

Depends on / 依赖: riemannZeta
-/
noncomputable def riemannZeta₀ (s : Complex) : Complex :=
  if s = 1 then γ else riemannZeta s - (s-1)⁻¹

/--
Definition of `riemannZeta₁` / `riemannZeta₁` 的定义

English:
definition riemannZeta₁
  signature: (s : Complex)
  body: 1 + (s - 1) * riemannZeta₀ s

@[simp]

中文:
定义 riemannZeta₁
  签名: (s : 复形)
  定义体: 1 + (s - 1) * riemannZeta₀ s

@[simp]
-/
noncomputable def riemannZeta₁ (s : Complex) : Complex := 1 + (s - 1) * riemannZeta₀ s

@[simp]
/--
lemma `riemannZeta₀_one` / 引理 `riemannZeta₀_one`

English:
lemma riemannZeta₀_one
  statement: riemannZeta₀ 1 = γ
  proof: by simp [riemannZeta₀]

@[simp]

中文:
引理 riemannZeta₀_one
  结论: riemannZeta₀ 1 = γ
  证明: by simp [riemannZeta₀]

@[simp]
-/
lemma riemannZeta₀_one : riemannZeta₀ 1 = γ := by simp [riemannZeta₀]

@[simp]
/--
lemma `riemannZeta₁_one` / 引理 `riemannZeta₁_one`

English:
lemma riemannZeta₁_one
  statement: riemannZeta₁ 1 = 1
  proof: by simp [riemannZeta₁]

中文:
引理 riemannZeta₁_one
  结论: riemannZeta₁ 1 = 1
  证明: by simp [riemannZeta₁]
-/
lemma riemannZeta₁_one : riemannZeta₁ 1 = 1 := by simp [riemannZeta₁]

/--
lemma `riemannZeta_eq_inv_sub_add` / 引理 `riemannZeta_eq_inv_sub_add`

English:
lemma riemannZeta_eq_inv_sub_add
  given: {s : Complex} (hs : s != 1)
  proof: by simp [riemannZeta₀, hs]

中文:
引理 riemannZeta_eq_inv_sub_add
  条件: {s : 复形} (hs : s != 1)
  证明: by simp [riemannZeta₀, hs]
-/
lemma riemannZeta_eq_inv_sub_add {s : Complex} (hs : s != 1) :
    riemannZeta s = (s - 1)⁻¹ + riemannZeta₀ s := by simp [riemannZeta₀, hs]

/--
lemma `riemannZeta_eq_inv_sub_mul` / 引理 `riemannZeta_eq_inv_sub_mul`

English:
lemma riemannZeta_eq_inv_sub_mul
  given: {s : Complex} (hs : s != 1)
  proof: by grind [riemannZeta₁, riemannZeta₀]

@[fun_prop]

中文:
引理 riemannZeta_eq_inv_sub_mul
  条件: {s : 复形} (hs : s != 1)
  证明: by grind [riemannZeta₁, riemannZeta₀]

@[fun_prop]
-/
lemma riemannZeta_eq_inv_sub_mul {s : Complex} (hs : s != 1) :
    riemannZeta s = (s - 1)⁻¹ * riemannZeta₁ s := by grind [riemannZeta₁, riemannZeta₀]

@[fun_prop]
/--
lemma `differentiable_riemannZeta₀` / 引理 `differentiable_riemannZeta₀`

English:
lemma differentiable_riemannZeta₀
  statement: Differentiable Complex riemannZeta₀
  proof: by
  rw [← differentiableOn_univ]; rw [← differentiableOn_compl_singleton_and_continuousAt_iff
    (univ_mem : _ in 𝓝 (1 : Complex))]; rw [continuousAt_iff_punctured_nhds]; rw [← compl_eq_univ_sdiff]
  constructor
  · refine .congr (f := fun s => riemannZeta s - (s - 1)⁻¹) ?_ (by simp +contextual [riemannZeta₀])
    exact differentiableOn_riemannZeta.fun_sub (by fun_prop (disch := grind))
  · convert tendsto_nhdsWithin_congr ?_ tendsto_riemannZeta_sub_one_div <;>
    simp +contextual [riemannZeta₀]

@[fun_prop]

中文:
引理 differentiable_riemannZeta₀
  结论: 可微 复形 riemannZeta₀
  证明: by
  rw [← differentiableOn_univ]; rw [← differentiableOn_compl_singleton_and_continuousAt_iff
    (univ_mem : _ in 𝓝 (1 : Complex))]; rw [continuousAt_iff_punctured_nhds]; rw [← compl_eq_univ_sdiff]
  constructor
  · refine .congr (f := fun s => riemannZeta s - (s - 1)⁻¹) ?_ (by simp +contextual [riemannZeta₀])
    exact differentiableOn_riemannZeta.fun_sub (by fun_prop (disch := grind))
  · convert tendsto_nhdsWithin_congr ?_ tendsto_riemannZeta_sub_one_div <;>
    simp +contextual [riemannZeta₀]

@[fun_prop]

Depends on / 依赖: compl_eq_univ_sdiff, contextual, continuousAt_iff_punctured_nhds, convert, differentiableOn_compl_singleton_and_continuousAt_iff, differentiableOn_riemannZeta, differentiableOn_riemannZeta.fun_sub, differentiableOn_univ, fun_prop, fun_sub, riemannZeta, tendsto_nhdsWithin_congr, tendsto_riemannZeta_sub_one_div, univ_mem
-/
lemma differentiable_riemannZeta₀ : Differentiable Complex riemannZeta₀ := by
  rw [← differentiableOn_univ]; rw [← differentiableOn_compl_singleton_and_continuousAt_iff
    (univ_mem : _ in 𝓝 (1 : Complex))]; rw [continuousAt_iff_punctured_nhds]; rw [← compl_eq_univ_sdiff]
  constructor
  · refine .congr (f := fun s => riemannZeta s - (s - 1)⁻¹) ?_ (by simp +contextual [riemannZeta₀])
    exact differentiableOn_riemannZeta.fun_sub (by fun_prop (disch := grind))
  · convert tendsto_nhdsWithin_congr ?_ tendsto_riemannZeta_sub_one_div <;>
    simp +contextual [riemannZeta₀]

@[fun_prop]
/--
lemma `differentiable_riemannZeta₁` / 引理 `differentiable_riemannZeta₁`

English:
lemma differentiable_riemannZeta₁
  statement: Differentiable Complex riemannZeta₁
  proof: by
  unfold riemannZeta₁; fun_prop

中文:
引理 differentiable_riemannZeta₁
  结论: 可微 复形 riemannZeta₁
  证明: by
  unfold riemannZeta₁; fun_prop

Depends on / 依赖: fun_prop
-/
lemma differentiable_riemannZeta₁ : Differentiable Complex riemannZeta₁ := by
  unfold riemannZeta₁; fun_prop

/--
lemma `riemannZeta₁_ne_zero_of_near_one` / 引理 `riemannZeta₁_ne_zero_of_near_one`

English:
lemma riemannZeta₁_ne_zero_of_near_one
  statement: forallᶠ s in 𝓝 1, riemannZeta₁ s != 0
  proof: by
  refine Tendsto.eventually_ne ?_ one_ne_zero
  simpa using (differentiable_riemannZeta₁.continuous.continuousAt (x := 1)).tendsto

@[simp]

中文:
引理 riemannZeta₁_ne_zero_of_near_one
  结论: 对任意ᶠ s in 𝓝 1, riemannZeta₁ s != 0
  证明: by
  refine Tendsto.eventually_ne ?_ one_ne_zero
  simpa using (differentiable_riemannZeta₁.continuous.continuousAt (x := 1)).tendsto

@[simp]

Depends on / 依赖: Tendsto, Tendsto.eventually_ne, continuous, continuous.continuousAt, continuousAt, eventually_ne, one_ne_zero, tendsto
-/
lemma riemannZeta₁_ne_zero_of_near_one : forallᶠ s in 𝓝 1, riemannZeta₁ s != 0 := by
  refine Tendsto.eventually_ne ?_ one_ne_zero
  simpa using (differentiable_riemannZeta₁.continuous.continuousAt (x := 1)).tendsto

@[simp]
/--
lemma `deriv_riemannZeta₁_one` / 引理 `deriv_riemannZeta₁_one`

English:
lemma deriv_riemannZeta₁_one
  statement: deriv riemannZeta₁ 1 = γ
  proof: by
  unfold riemannZeta₁
  rw [deriv_const_add]; rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp

中文:
引理 deriv_riemannZeta₁_one
  结论: deriv riemannZeta₁ 1 = γ
  证明: by
  unfold riemannZeta₁
  rw [deriv_const_add]; rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp

Depends on / 依赖: deriv_const_add, deriv_fun_mul, fun_prop
-/
lemma deriv_riemannZeta₁_one : deriv riemannZeta₁ 1 = γ := by
  unfold riemannZeta₁
  rw [deriv_const_add]; rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp

/--
lemma `deriv_riemannZeta_eq_neg_inv_sub_sq_add` / 引理 `deriv_riemannZeta_eq_neg_inv_sub_sq_add`

English:
lemma deriv_riemannZeta_eq_neg_inv_sub_sq_add
  given: {s : Complex} (hs : s != 1)
  proof: by
  have := sub_ne_zero_of_ne hs
  convert EventuallyEq.deriv_eq (f := fun s => (s - 1)⁻¹ + riemannZeta₀ s) ?_
  · rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_fun_inv'' (by fun_prop) (by exact this)]
    simp [field]
  · filter_upwards [compl_singleton_mem_nhds hs] using by grind [riemannZeta_eq_inv_sub_add]

中文:
引理 deriv_riemannZeta_eq_neg_inv_sub_sq_add
  条件: {s : 复形} (hs : s != 1)
  证明: by
  have := sub_ne_zero_of_ne hs
  convert EventuallyEq.deriv_eq (f := fun s => (s - 1)⁻¹ + riemannZeta₀ s) ?_
  · rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_fun_inv'' (by fun_prop) (by exact this)]
    simp [field]
  · filter_upwards [compl_singleton_mem_nhds hs] using by grind [riemannZeta_eq_inv_sub_add]

Depends on / 依赖: EventuallyEq, EventuallyEq.deriv_eq, compl_singleton_mem_nhds, convert, deriv_eq, deriv_fun_add, deriv_fun_inv, filter_upwards, fun_prop, riemannZeta_eq_inv_sub_add, sub_ne_zero_of_ne
-/
lemma deriv_riemannZeta_eq_neg_inv_sub_sq_add {s : Complex} (hs : s != 1) :
    deriv riemannZeta s = - ((s - 1)⁻¹) ^ 2 + deriv riemannZeta₀ s := by
  have := sub_ne_zero_of_ne hs
  convert EventuallyEq.deriv_eq (f := fun s => (s - 1)⁻¹ + riemannZeta₀ s) ?_
  · rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_fun_inv'' (by fun_prop) (by exact this)]
    simp [field]
  · filter_upwards [compl_singleton_mem_nhds hs] using by grind [riemannZeta_eq_inv_sub_add]

/--
lemma `deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add` / 引理 `deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add`

English:
lemma deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add
  given: {s : Complex} (hs : s != 1)
  proof: by
  have := sub_ne_zero_of_ne hs
  convert EventuallyEq.deriv_eq (f := fun s => (s - 1)⁻¹ * riemannZeta₁ s) ?_
  · rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_fun_inv'' (by fun_prop) (by exact this)]
    simp [field]
  · filter_upwards [compl_singleton_mem_nhds hs] using by grind [riemannZeta_eq_inv_sub_mul]

中文:
引理 deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add
  条件: {s : 复形} (hs : s != 1)
  证明: by
  have := sub_ne_zero_of_ne hs
  convert EventuallyEq.deriv_eq (f := fun s => (s - 1)⁻¹ * riemannZeta₁ s) ?_
  · rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_fun_inv'' (by fun_prop) (by exact this)]
    simp [field]
  · filter_upwards [compl_singleton_mem_nhds hs] using by grind [riemannZeta_eq_inv_sub_mul]

Depends on / 依赖: EventuallyEq, EventuallyEq.deriv_eq, compl_singleton_mem_nhds, convert, deriv_eq, deriv_fun_inv, deriv_fun_mul, filter_upwards, fun_prop, riemannZeta_eq_inv_sub_mul, sub_ne_zero_of_ne
-/
lemma deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add {s : Complex} (hs : s != 1) :
    deriv riemannZeta s =
      - ((s - 1)⁻¹) ^ 2 * (riemannZeta₁ s) + (s - 1)⁻¹ * deriv riemannZeta₁ s := by
  have := sub_ne_zero_of_ne hs
  convert EventuallyEq.deriv_eq (f := fun s => (s - 1)⁻¹ * riemannZeta₁ s) ?_
  · rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_fun_inv'' (by fun_prop) (by exact this)]
    simp [field]
  · filter_upwards [compl_singleton_mem_nhds hs] using by grind [riemannZeta_eq_inv_sub_mul]

/--
lemma `deriv_riemannZeta_add_inv_sub_sq_bounded` / 引理 `deriv_riemannZeta_add_inv_sub_sq_bounded`

English:
lemma deriv_riemannZeta_add_inv_sub_sq_bounded
  proof: (differentiable_riemannZeta₀.deriv.continuous.continuousAt.isBigO.mono nhdsWithin_le_nhds).congr'
  (eventually_nhdsWithin_of_forall (by simp +contextual [deriv_riemannZeta_eq_neg_inv_sub_sq_add]))
  .rfl

中文:
引理 deriv_riemannZeta_add_inv_sub_sq_bounded
  证明: (differentiable_riemannZeta₀.deriv.continuous.continuousAt.isBigO.mono nhdsWithin_le_nhds).congr'
  (eventually_nhdsWithin_of_forall (by simp +contextual [deriv_riemannZeta_eq_neg_inv_sub_sq_add]))
  .rfl

Depends on / 依赖: contextual, continuous, continuousAt, deriv.continuous.continuousAt.isBigO.mono, deriv_riemannZeta_eq_neg_inv_sub_sq_add, eventually_nhdsWithin_of_forall, isBigO, nhdsWithin_le_nhds
-/
lemma deriv_riemannZeta_add_inv_sub_sq_bounded :
    (fun s => deriv riemannZeta s + ((s - 1)⁻¹) ^ 2) =O[𝓝[!=] 1] (fun _ => (1 : Complex)) :=
  (differentiable_riemannZeta₀.deriv.continuous.continuousAt.isBigO.mono nhdsWithin_le_nhds).congr'
  (eventually_nhdsWithin_of_forall (by simp +contextual [deriv_riemannZeta_eq_neg_inv_sub_sq_add]))
  .rfl

/--
lemma `log_riemannZeta_eq_neg_log_sub_add_ofReal` / 引理 `log_riemannZeta_eq_neg_log_sub_add_ofReal`

English:
lemma log_riemannZeta_eq_neg_log_sub_add_ofReal
  given: {s : Real} (hs : s > 1)
  proof: by
  have : (riemannZeta s).re = (s - 1)⁻¹ * (riemannZeta₁ s).re := by
    rw_mod_cast [riemannZeta_eq_inv_sub_mul (by aesop), re_ofReal_mul]
  rw [this]; rw [Real.log_mul]; rw [Real.log_inv] <;>
  grind [riemannZeta_re_pos_of_one_lt hs]

中文:
引理 log_riemannZeta_eq_neg_log_sub_add_of实数
  条件: {s : 实数} (hs : s > 1)
  证明: by
  have : (riemannZeta s).re = (s - 1)⁻¹ * (riemannZeta₁ s).re := by
    rw_mod_cast [riemannZeta_eq_inv_sub_mul (by aesop), re_ofReal_mul]
  rw [this]; rw [Real.log_mul]; rw [Real.log_inv] <;>
  grind [riemannZeta_re_pos_of_one_lt hs]

Depends on / 依赖: Real.log_inv, Real.log_mul, log_inv, log_mul, re_ofReal_mul, riemannZeta, riemannZeta_eq_inv_sub_mul, riemannZeta_re_pos_of_one_lt, rw_mod_cast
-/
lemma log_riemannZeta_eq_neg_log_sub_add_ofReal {s : Real} (hs : s > 1) :
    (riemannZeta s).re.log = - (s - 1).log + (riemannZeta₁ s).re.log := by
  have : (riemannZeta s).re = (s - 1)⁻¹ * (riemannZeta₁ s).re := by
    rw_mod_cast [riemannZeta_eq_inv_sub_mul (by aesop), re_ofReal_mul]
  rw [this]; rw [Real.log_mul]; rw [Real.log_inv] <;>
  grind [riemannZeta_re_pos_of_one_lt hs]

/--
lemma `log_riemannZeta_add_log_sub_isBigO_ofReal` / 引理 `log_riemannZeta_add_log_sub_isBigO_ofReal`

English:
lemma log_riemannZeta_add_log_sub_isBigO_ofReal
  proof: by
  suffices (fun (s : Real) => (riemannZeta₁ s).re.log) =O[𝓝 1] (· - 1) by
    refine (this.mono nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall (fun s hs => ?_)) .rfl
    simp [log_riemannZeta_eq_neg_log_sub_add_ofReal hs]
  suffices DifferentiableAt Real (fun (s : Real) => (riemannZeta₁ s).re.log) 1 by
    simpa using this.isBigO_sub
  have : Differentiable Real riemannZeta₀ := by fun_prop
  fun_prop (disch := simp)

中文:
引理 log_riemannZeta_add_log_sub_isBigO_of实数
  证明: by
  suffices (fun (s : Real) => (riemannZeta₁ s).re.log) =O[𝓝 1] (· - 1) by
    refine (this.mono nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall (fun s hs => ?_)) .rfl
    simp [log_riemannZeta_eq_neg_log_sub_add_ofReal hs]
  suffices DifferentiableAt Real (fun (s : Real) => (riemannZeta₁ s).re.log) 1 by
    simpa using this.isBigO_sub
  have : Differentiable Real riemannZeta₀ := by fun_prop
  fun_prop (disch := simp)

Depends on / 依赖: Differentiable, DifferentiableAt, eventually_nhdsWithin_of_forall, fun_prop, isBigO_sub, log_riemannZeta_eq_neg_log_sub_add_ofReal, nhdsWithin_le_nhds, re.log, this.isBigO_sub, this.mono
-/
lemma log_riemannZeta_add_log_sub_isBigO_ofReal :
    (fun (s : Real) => (riemannZeta s).re.log + (s - 1).log) =O[𝓝[>] 1] (· - 1) := by
  suffices (fun (s : Real) => (riemannZeta₁ s).re.log) =O[𝓝 1] (· - 1) by
    refine (this.mono nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall (fun s hs => ?_)) .rfl
    simp [log_riemannZeta_eq_neg_log_sub_add_ofReal hs]
  suffices DifferentiableAt Real (fun (s : Real) => (riemannZeta₁ s).re.log) 1 by
    simpa using this.isBigO_sub
  have : Differentiable Real riemannZeta₀ := by fun_prop
  fun_prop (disch := simp)

/--
lemma `log_riemannZeta_add_log_sub_isLittleO_ofReal` / 引理 `log_riemannZeta_add_log_sub_isLittleO_ofReal`

English:
lemma log_riemannZeta_add_log_sub_isLittleO_ofReal
  proof: log_riemannZeta_add_log_sub_isBigO_ofReal.trans_isLittleO
    (continuous_id.continuousAt.isLittleO.mono nhdsWithin_le_nhds)

中文:
引理 log_riemannZeta_add_log_sub_isLittleO_of实数
  证明: log_riemannZeta_add_log_sub_isBigO_ofReal.trans_isLittleO
    (continuous_id.continuousAt.isLittleO.mono nhdsWithin_le_nhds)

Depends on / 依赖: continuousAt, continuous_id, continuous_id.continuousAt.isLittleO.mono, isLittleO, log_riemannZeta_add_log_sub_isBigO_ofReal, log_riemannZeta_add_log_sub_isBigO_ofReal.trans_isLittleO, nhdsWithin_le_nhds, trans_isLittleO
-/
lemma log_riemannZeta_add_log_sub_isLittleO_ofReal :
    (fun (s : Real) => (riemannZeta s).re.log + (s - 1).log) =o[𝓝[>] (1 : Real)] (fun _ => (1 : Real)) :=
  log_riemannZeta_add_log_sub_isBigO_ofReal.trans_isLittleO
    (continuous_id.continuousAt.isLittleO.mono nhdsWithin_le_nhds)

/--
lemma `log_deriv_riemannZeta_eq_neg_inv_sub_add` / 引理 `log_deriv_riemannZeta_eq_neg_inv_sub_add`

English:
lemma log_deriv_riemannZeta_eq_neg_inv_sub_add
  proof: by
  filter_upwards [eventually_mem_nhdsWithin,
    riemannZeta₁_ne_zero_of_near_one.filter_mono nhdsWithin_le_nhds]
  grind [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add, riemannZeta_eq_inv_sub_mul]

中文:
引理 log_deriv_riemannZeta_eq_neg_inv_sub_add
  证明: by
  filter_upwards [eventually_mem_nhdsWithin,
    riemannZeta₁_ne_zero_of_near_one.filter_mono nhdsWithin_le_nhds]
  grind [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add, riemannZeta_eq_inv_sub_mul]

Depends on / 依赖: _ne_zero_of_near_one.filter_mono, deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add, eventually_mem_nhdsWithin, filter_mono, filter_upwards, nhdsWithin_le_nhds, riemannZeta_eq_inv_sub_mul
-/
lemma log_deriv_riemannZeta_eq_neg_inv_sub_add :
    forallᶠ s in 𝓝[!=] 1, (deriv riemannZeta s) / (riemannZeta s)
    = - (s - 1)⁻¹ + (deriv riemannZeta₁ s) / (riemannZeta₁ s) := by
  filter_upwards [eventually_mem_nhdsWithin,
    riemannZeta₁_ne_zero_of_near_one.filter_mono nhdsWithin_le_nhds]
  grind [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add, riemannZeta_eq_inv_sub_mul]

/--
lemma `log_deriv_riemannZeta_add_inv_sub_sub_isBigO` / 引理 `log_deriv_riemannZeta_add_inv_sub_sub_isBigO`

English:
lemma log_deriv_riemannZeta_add_inv_sub_sub_isBigO
  proof: by
  suffices (fun s => (deriv riemannZeta₁ s) / (riemannZeta₁ s) - γ) =O[𝓝 1] (· - 1) by
    refine (this.mono nhdsWithin_le_nhds).congr' ?_ .rfl
    filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add]
    simp +contextual
  suffices DifferentiableAt Complex (fun s => (deriv riemannZeta₁ s) / (riemannZeta₁ s)) 1 by
    simpa using this.isBigO_sub
  fun_prop (disch := simp)

中文:
引理 log_deriv_riemannZeta_add_inv_sub_sub_isBigO
  证明: by
  suffices (fun s => (deriv riemannZeta₁ s) / (riemannZeta₁ s) - γ) =O[𝓝 1] (· - 1) by
    refine (this.mono nhdsWithin_le_nhds).congr' ?_ .rfl
    filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add]
    simp +contextual
  suffices DifferentiableAt Complex (fun s => (deriv riemannZeta₁ s) / (riemannZeta₁ s)) 1 by
    simpa using this.isBigO_sub
  fun_prop (disch := simp)

Depends on / 依赖: DifferentiableAt, contextual, filter_upwards, fun_prop, isBigO_sub, log_deriv_riemannZeta_eq_neg_inv_sub_add, nhdsWithin_le_nhds, this.isBigO_sub, this.mono
-/
lemma log_deriv_riemannZeta_add_inv_sub_sub_isBigO :
    (fun s => (deriv riemannZeta s) / (riemannZeta s) + (s - 1)⁻¹ - γ)
    =O[𝓝[!=] 1] (· - 1) := by
  suffices (fun s => (deriv riemannZeta₁ s) / (riemannZeta₁ s) - γ) =O[𝓝 1] (· - 1) by
    refine (this.mono nhdsWithin_le_nhds).congr' ?_ .rfl
    filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add]
    simp +contextual
  suffices DifferentiableAt Complex (fun s => (deriv riemannZeta₁ s) / (riemannZeta₁ s)) 1 by
    simpa using this.isBigO_sub
  fun_prop (disch := simp)

/--
lemma `log_deriv_riemannZeta_add_inv_sub_sub_isLittleO` / 引理 `log_deriv_riemannZeta_add_inv_sub_sub_isLittleO`

English:
lemma log_deriv_riemannZeta_add_inv_sub_sub_isLittleO
  proof: log_deriv_riemannZeta_add_inv_sub_sub_isBigO.trans_isLittleO
    (continuous_id.continuousAt.isLittleO.mono nhdsWithin_le_nhds)

中文:
引理 log_deriv_riemannZeta_add_inv_sub_sub_isLittleO
  证明: log_deriv_riemannZeta_add_inv_sub_sub_isBigO.trans_isLittleO
    (continuous_id.continuousAt.isLittleO.mono nhdsWithin_le_nhds)

Depends on / 依赖: continuousAt, continuous_id, continuous_id.continuousAt.isLittleO.mono, isLittleO, log_deriv_riemannZeta_add_inv_sub_sub_isBigO, log_deriv_riemannZeta_add_inv_sub_sub_isBigO.trans_isLittleO, nhdsWithin_le_nhds, trans_isLittleO
-/
lemma log_deriv_riemannZeta_add_inv_sub_sub_isLittleO :
    (fun s => (deriv riemannZeta s) / (riemannZeta s) + (s - 1)⁻¹ - γ)
    =o[𝓝[!=] 1] (fun _ => (1 : Complex)) :=
  log_deriv_riemannZeta_add_inv_sub_sub_isBigO.trans_isLittleO
    (continuous_id.continuousAt.isLittleO.mono nhdsWithin_le_nhds)

/--
lemma `log_deriv_riemannZeta_add_inv_sub_bounded` / 引理 `log_deriv_riemannZeta_add_inv_sub_bounded`

English:
lemma log_deriv_riemannZeta_add_inv_sub_bounded
  proof: (isBigO_const_one ..).sub_iff_left.mp log_deriv_riemannZeta_add_inv_sub_sub_isLittleO.isBigO

中文:
引理 log_deriv_riemannZeta_add_inv_sub_bounded
  证明: (isBigO_const_one ..).sub_iff_left.mp log_deriv_riemannZeta_add_inv_sub_sub_isLittleO.isBigO

Depends on / 依赖: isBigO, isBigO_const_one, log_deriv_riemannZeta_add_inv_sub_sub_isLittleO, log_deriv_riemannZeta_add_inv_sub_sub_isLittleO.isBigO, sub_iff_left, sub_iff_left.mp
-/
lemma log_deriv_riemannZeta_add_inv_sub_bounded :
    (fun s => (deriv riemannZeta s) / (riemannZeta s) + (s - 1)⁻¹)
    =O[𝓝[!=] 1] (fun _ => (1 : Complex)) :=
  (isBigO_const_one ..).sub_iff_left.mp log_deriv_riemannZeta_add_inv_sub_sub_isLittleO.isBigO

/--
lemma `inv_riemannZeta_eq_sub_mul` / 引理 `inv_riemannZeta_eq_sub_mul`

English:
lemma inv_riemannZeta_eq_sub_mul
  proof: by
  filter_upwards [eventually_mem_nhdsWithin,
    riemannZeta₁_ne_zero_of_near_one.filter_mono nhdsWithin_le_nhds] with s hs
  simp [riemannZeta_eq_inv_sub_mul hs, field]

中文:
引理 inv_riemannZeta_eq_sub_mul
  证明: by
  filter_upwards [eventually_mem_nhdsWithin,
    riemannZeta₁_ne_zero_of_near_one.filter_mono nhdsWithin_le_nhds] with s hs
  simp [riemannZeta_eq_inv_sub_mul hs, field]

Depends on / 依赖: _ne_zero_of_near_one.filter_mono, eventually_mem_nhdsWithin, filter_mono, filter_upwards, nhdsWithin_le_nhds, riemannZeta_eq_inv_sub_mul
-/
lemma inv_riemannZeta_eq_sub_mul :
    forallᶠ s in 𝓝[!=] 1, (riemannZeta s)⁻¹ = (s - 1) * (riemannZeta₁ s)⁻¹ := by
  filter_upwards [eventually_mem_nhdsWithin,
    riemannZeta₁_ne_zero_of_near_one.filter_mono nhdsWithin_le_nhds] with s hs
  simp [riemannZeta_eq_inv_sub_mul hs, field]

/--
lemma `inv_riemannZeta_sub_sub_isBigO` / 引理 `inv_riemannZeta_sub_sub_isBigO`

English:
lemma inv_riemannZeta_sub_sub_isBigO
  proof: by
  suffices (fun s => (s - 1) * ((riemannZeta₁ s)⁻¹ - 1)) =O[𝓝 1] (fun s => (s - 1) ^ 2) by
    refine (this.mono nhdsWithin_le_nhds).congr' ?_ .rfl
    filter_upwards [inv_riemannZeta_eq_sub_mul]
    simp +contextual [field]
  suffices (fun s => ((riemannZeta₁ s)⁻¹ - 1)) =O[𝓝 1] (· - 1) by
    simpa [pow_two] using (isBigO_refl ..).mul this
  simpa using ((differentiable_riemannZeta₁.differentiableAt (x := 1)).inv (by simp)).isBigO_sub

中文:
引理 inv_riemannZeta_sub_sub_isBigO
  证明: by
  suffices (fun s => (s - 1) * ((riemannZeta₁ s)⁻¹ - 1)) =O[𝓝 1] (fun s => (s - 1) ^ 2) by
    refine (this.mono nhdsWithin_le_nhds).congr' ?_ .rfl
    filter_upwards [inv_riemannZeta_eq_sub_mul]
    simp +contextual [field]
  suffices (fun s => ((riemannZeta₁ s)⁻¹ - 1)) =O[𝓝 1] (· - 1) by
    simpa [pow_two] using (isBigO_refl ..).mul this
  simpa using ((differentiable_riemannZeta₁.differentiableAt (x := 1)).inv (by simp)).isBigO_sub

Depends on / 依赖: contextual, differentiableAt, filter_upwards, inv_riemannZeta_eq_sub_mul, isBigO_refl, isBigO_sub, nhdsWithin_le_nhds, pow_two, this.mono
-/
lemma inv_riemannZeta_sub_sub_isBigO :
    (fun s => (riemannZeta s)⁻¹ - (s - 1)) =O[𝓝[!=] 1] (fun s => (s - 1) ^ 2) := by
  suffices (fun s => (s - 1) * ((riemannZeta₁ s)⁻¹ - 1)) =O[𝓝 1] (fun s => (s - 1) ^ 2) by
    refine (this.mono nhdsWithin_le_nhds).congr' ?_ .rfl
    filter_upwards [inv_riemannZeta_eq_sub_mul]
    simp +contextual [field]
  suffices (fun s => ((riemannZeta₁ s)⁻¹ - 1)) =O[𝓝 1] (· - 1) by
    simpa [pow_two] using (isBigO_refl ..).mul this
  simpa using ((differentiable_riemannZeta₁.differentiableAt (x := 1)).inv (by simp)).isBigO_sub

/--
lemma `inv_riemannZeta_sub_sub_isLittleO` / 引理 `inv_riemannZeta_sub_sub_isLittleO`

English:
lemma inv_riemannZeta_sub_sub_isLittleO
  proof: by
  apply inv_riemannZeta_sub_sub_isBigO.trans_isLittleO
  suffices (· - 1) =o[𝓝 1] (fun _ : Complex => (1 : Complex)) by
    simpa [pow_two] using (this.mul_isBigO <| isBigO_refl ..).mono nhdsWithin_le_nhds
  exact ContinuousAt.isLittleO (by fun_prop)

中文:
引理 inv_riemannZeta_sub_sub_isLittleO
  证明: by
  apply inv_riemannZeta_sub_sub_isBigO.trans_isLittleO
  suffices (· - 1) =o[𝓝 1] (fun _ : Complex => (1 : Complex)) by
    simpa [pow_two] using (this.mul_isBigO <| isBigO_refl ..).mono nhdsWithin_le_nhds
  exact ContinuousAt.isLittleO (by fun_prop)

Depends on / 依赖: ContinuousAt, ContinuousAt.isLittleO, fun_prop, inv_riemannZeta_sub_sub_isBigO, inv_riemannZeta_sub_sub_isBigO.trans_isLittleO, isBigO_refl, isLittleO, mul_isBigO, nhdsWithin_le_nhds, pow_two, this.mul_isBigO, trans_isLittleO
-/
lemma inv_riemannZeta_sub_sub_isLittleO :
    (fun s => (riemannZeta s)⁻¹ - (s - 1)) =o[𝓝[!=] 1] (· - 1) := by
  apply inv_riemannZeta_sub_sub_isBigO.trans_isLittleO
  suffices (· - 1) =o[𝓝 1] (fun _ : Complex => (1 : Complex)) by
    simpa [pow_two] using (this.mul_isBigO <| isBigO_refl ..).mono nhdsWithin_le_nhds
  exact ContinuousAt.isLittleO (by fun_prop)

/--
lemma `inv_riemannZeta_isBigO` / 引理 `inv_riemannZeta_isBigO`

English:
lemma inv_riemannZeta_isBigO
  proof: (isBigO_refl ..).sub_iff_left.mp inv_riemannZeta_sub_sub_isLittleO.isBigO

中文:
引理 inv_riemannZeta_isBigO
  证明: (isBigO_refl ..).sub_iff_left.mp inv_riemannZeta_sub_sub_isLittleO.isBigO

Depends on / 依赖: inv_riemannZeta_sub_sub_isLittleO, inv_riemannZeta_sub_sub_isLittleO.isBigO, isBigO, isBigO_refl, sub_iff_left, sub_iff_left.mp
-/
lemma inv_riemannZeta_isBigO :
    (fun s => (riemannZeta s)⁻¹) =O[𝓝[!=] 1] (· - 1) :=
  (isBigO_refl ..).sub_iff_left.mp inv_riemannZeta_sub_sub_isLittleO.isBigO

end near_one
