/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Convexity properties of the Gamma function

In this file, we prove that `Gamma` and `log ∘ Gamma` are convex functions on the positive real
line. We then prove the Bohr-Mollerup theorem, which characterises `Gamma` as the *unique*
positive-real-valued, log-convex function on the positive reals satisfying `f (x + 1) = x f x` and
`f 1 = 1`.

The proof of the Bohr-Mollerup theorem is bound up with the proof of (a weak form of) the Euler
limit formula, `Real.BohrMollerup.tendsto_logGammaSeq`, stating that for positive
real `x` the sequence `x * log n + log n! - ∑ (m : ℕ) ∈ Finset.range (n + 1), log (x + m)`
tends to `log Γ(x)` as `n → ∞`. We prove that any function satisfying the hypotheses of the
Bohr-Mollerup theorem must agree with the limit in the Euler limit formula, so there is at most one
such function; then we show that `Γ` satisfies these conditions.

Since most of the auxiliary lemmas for the Bohr-Mollerup theorem are of no relevance outside the
context of this proof, we place them in a separate namespace `Real.BohrMollerup` to avoid clutter.
(This includes the logarithmic form of the Euler limit formula, since later we will prove a more
general form of the Euler limit formula valid for any real or complex `x`; see
`Real.Gamma_seq_tendsto_Gamma` and `Complex.Gamma_seq_tendsto_Gamma` in the file
`Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`.)

As an application of the Bohr-Mollerup theorem we prove the Legendre doubling formula for the
Gamma function for real positive `s` (which will be upgraded to a proof for all complex `s` in a
later file).

TODO: This argument can be extended to prove the general `k`-multiplication formula (at least up
to a constant, and it should be possible to deduce the value of this constant using Stirling's
formula).
-/

@[expose] public section


noncomputable section

open Filter Set MeasureTheory

open scoped Nat ENNReal Topology Real

namespace Real

local notation "Γ" => Gamma

section Convexity

/--
theorem `Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma` / 定理 `Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma`

English:
theorem Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
  statement: {s t a b : Real} (hs : 0 < s) (ht : 0 < t)
  proof: by
  -- We will apply Hölder's inequality, for the conjugate exponents `p = 1 / a`
  -- and `q = 1 / b`, to the functions `f a s` and `f b t`, where `f` is as follows:
  let f : Real -> Real -> Real -> Real := fun c u x => exp (-c * x) * x ^ (c * (u - 1))
  have e : HolderConjugate (1 / a) (1 / b) :

中文:
定理 Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
  结论: {s t a b : 实数} (hs : 0 < s) (ht : 0 < t)
  证明: by
  -- We will apply Hölder's inequality, for the conjugate exponents `p = 1 / a`
  -- and `q = 1 / b`, to the functions `f a s` and `f b t`, where `f` is as follows:
  let f : Real -> Real -> Real -> Real := fun c u x => exp (-c * x) * x ^ (c * (u - 1))
  have e : HolderConjugate (1 / a) (1 / b) :
-/
theorem Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma {s t a b : Real} (hs : 0 < s) (ht : 0 < t)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    Gamma (a * s + b * t) <= Gamma s ^ a * Gamma t ^ b := by
  -- We will apply Hölder's inequality, for the conjugate exponents `p = 1 / a`
  -- and `q = 1 / b`, to the functions `f a s` and `f b t`, where `f` is as follows:
  let f : Real -> Real -> Real -> Real := fun c u x => exp (-c * x) * x ^ (c * (u - 1))
  have e : HolderConjugate (1 / a) (1 / b) := Real.holderConjugate_one_div ha hb hab
  have hab' : b = 1 - a := by linarith
  have hst : 0 < a * s + b * t := by positivity
  -- some properties of f:
  have posf : forall c u x : Real, x in Ioi (0 : Real) -> 0 <= f c u x := fun c u x hx =>
    mul_nonneg (exp_pos _).le (rpow_pos_of_pos hx _).le
  have posf' : forall c u : Real, forallᵐ x : Real ∂volume.restrict (Ioi 0), 0 <= f c u x := fun c u =>
    (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (posf c u))
  have fpow :
    forall {c x : Real} (_ : 0 < c) (u : Real) (_ : 0 < x), exp (-x) * x ^ (u - 1) = f c u x ^ (1 / c) := by
    intro c x hc u hx
    dsimp only [f]
    rw [mul_rpow (exp_pos _).le ((rpow_nonneg hx.le) _)]; rw [← exp_mul]; rw [← rpow_mul hx.le]
    congr 2 <;> field
  -- show `f c u` is in `ℒp` for `p = 1/c`:
  have f_mem_Lp :
    forall {c u : Real} (hc : 0 < c) (hu : 0 < u),
      MemLp (f c u) (ENNReal.ofReal (1 / c)) (volume.restrict (Ioi 0)) := by
    intro c u hc hu
    have A : ENNReal.ofReal (1 / c) != 0 := by
      rwa [Ne, ENNReal.ofReal_eq_zero, not_le, one_div_pos]
    have B : ENNReal.ofReal (1 / c) != ∞ := ENNReal.ofReal_ne_top
    rw [← memLp_norm_rpow_iff _ A B]; rw [ENNReal.toReal_ofReal (one_div_nonneg.mpr hc.le)]; rw [ENNReal.div_self A B]; rw [memLp_one_iff_integrable]
    · apply Integrable.congr (GammaIntegral_convergent hu)
      refine eventuallyEq_of_mem (self_mem_ae_restrict measurableSet_Ioi) fun x hx => ?_
      rw [fpow hc u hx]
      congr 1
      exact (norm_of_nonneg (posf _ _ x hx)).symm
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine .mul (by fun_prop) (continuousOn_of_forall_continuousAt fun x hx => ?_)
      exact continuousAt_rpow_const _ _ (Or.inl (mem_Ioi.mp hx).ne')
  -- now apply Hölder:
  rw [Gamma_eq_integral hs]; rw [Gamma_eq_integral ht]; rw [Gamma_eq_integral hst]
  convert!
    MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg e (posf' a s) (posf' b t) (f_mem_Lp ha hs)
      (f_mem_Lp hb ht) using 1
  · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have A : exp (-x) = exp (-a * x) * exp (-b * x) := by
      rw [← exp_add]; rw [← add_mul]; rw [← neg_add]; rw [hab]; rw [neg_one_mul]
    have B : x ^ (a * s + b * t - 1) = x ^ (a * (s - 1)) * x ^ (b * (t - 1)) := by
      rw [← rpow_add hx]; rw [hab']; congr 1; ring
    rw [A]; rw [B]
    ring
  · rw [one_div_one_div, one_div_one_div]
    congr 2 <;> exact setIntegral_congr_fun measurableSet_Ioi fun x hx => fpow (by assumption) _ hx

/--
theorem `convexOn_log_Gamma` / 定理 `convexOn_log_Gamma`

English:
theorem convexOn_log_Gamma
  statement: ConvexOn Real (Ioi 0) (log ∘ Gamma)
  proof: by
  refine convexOn_iff_forall_pos.mpr ⟨convex_Ioi _, fun x hx y hy a b ha hb hab => ?_⟩
  have : b = 1 - a := by linarith
  subst this
  simp_rw [Function.comp_apply, smul_eq_mul]
  push _ in _ at hx hy
  rw [← log_rpow]; rw [← log_rpow]; rw [← log_mul]
  · gcongr
    exact Gamma_mul_add_mul_le_rp

中文:
定理 convexOn_log_Gamma
  结论: ConvexOn 实数 (Ioi 0) (log ∘ Gamma)
  证明: by
  refine convexOn_iff_forall_pos.mpr ⟨convex_Ioi _, fun x hx y hy a b ha hb hab => ?_⟩
  have : b = 1 - a := by linarith
  subst this
  simp_rw [Function.comp_apply, smul_eq_mul]
  push _ in _ at hx hy
  rw [← log_rpow]; rw [← log_rpow]; rw [← log_mul]
  · gcongr
    exact Gamma_mul_add_mul_le_rp

Depends on / 依赖: Function, Function.comp_apply, Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma, all_goals, comp_apply, convexOn_iff_forall_pos, convexOn_iff_forall_pos.mpr, convex_Ioi, log_mul, log_rpow, simp_rw, smul_eq_mul
-/
theorem convexOn_log_Gamma : ConvexOn Real (Ioi 0) (log ∘ Gamma) := by
  refine convexOn_iff_forall_pos.mpr ⟨convex_Ioi _, fun x hx y hy a b ha hb hab => ?_⟩
  have : b = 1 - a := by linarith
  subst this
  simp_rw [Function.comp_apply, smul_eq_mul]
  push _ in _ at hx hy
  rw [← log_rpow]; rw [← log_rpow]; rw [← log_mul]
  · gcongr
    exact Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hx hy ha hb hab
  all_goals positivity

/--
theorem `convexOn_Gamma` / 定理 `convexOn_Gamma`

English:
theorem convexOn_Gamma
  statement: ConvexOn Real (Ioi 0) Gamma
  proof: by
  refine
    ((convexOn_exp.subset (subset_univ _) ?_).comp convexOn_log_Gamma
          (exp_monotone.monotoneOn _)).congr
      fun x hx => exp_log (Gamma_pos_of_pos hx)
  rw [convex_iff_isPreconnected]
  refine isPreconnected_Ioi.image _ fun x hx => ContinuousAt.continuousWithinAt ?_
  refine 

中文:
定理 convexOn_Gamma
  结论: ConvexOn 实数 (Ioi 0) Gamma
  证明: by
  refine
    ((convexOn_exp.subset (subset_univ _) ?_).comp convexOn_log_Gamma
          (exp_monotone.monotoneOn _)).congr
      fun x hx => exp_log (Gamma_pos_of_pos hx)
  rw [convex_iff_isPreconnected]
  refine isPreconnected_Ioi.image _ fun x hx => ContinuousAt.continuousWithinAt ?_
  refine 

Depends on / 依赖: ContinuousAt, ContinuousAt.continuousWithinAt, Gamma_pos_of_pos, Nat.cast_nonneg, add_pos_of_pos_of_nonneg, cast_nonneg, continuousAt, continuousAt.log, continuousWithinAt, convexOn_exp, convexOn_exp.subset, convexOn_log_Gamma, convex_iff_isPreconnected, differentiableAt_Gamma, exp_log, exp_monotone, exp_monotone.monotoneOn, isPreconnected_Ioi, isPreconnected_Ioi.image, mem_Ioi
-/
theorem convexOn_Gamma : ConvexOn Real (Ioi 0) Gamma := by
  refine
    ((convexOn_exp.subset (subset_univ _) ?_).comp convexOn_log_Gamma
          (exp_monotone.monotoneOn _)).congr
      fun x hx => exp_log (Gamma_pos_of_pos hx)
  rw [convex_iff_isPreconnected]
  refine isPreconnected_Ioi.image _ fun x hx => ContinuousAt.continuousWithinAt ?_
  refine (differentiableAt_Gamma fun m => ?_).continuousAt.log (Gamma_pos_of_pos hx).ne'
  exact (neg_lt_iff_pos_add.mpr (add_pos_of_pos_of_nonneg (mem_Ioi.mp hx) (Nat.cast_nonneg m))).ne'

end Convexity

section BohrMollerup

namespace BohrMollerup

/--
Definition of `logGammaSeq` / `logGammaSeq` 的定义

English:
definition logGammaSeq
  signature: (x : Real) (n : Nat)
  body: x * log n + log n ! - ∑ m in Finset.range (n + 1), log (x + m)

中文:
定义 logGammaSeq
  签名: (x : 实数) (n : 自然数)
  定义体: x * log n + log n ! - ∑ m in Finset.range (n + 1), log (x + m)

Depends on / 依赖: Finset, Finset.range
-/
def logGammaSeq (x : Real) (n : Nat) : Real :=
  x * log n + log n ! - ∑ m in Finset.range (n + 1), log (x + m)

variable {f : Real -> Real} {x : Real} {n : Nat}

/--
theorem `f_nat_eq` / 定理 `f_nat_eq`

English:
theorem f_nat_eq
  given: (hf_feq : forall {y : Real}, 0 < y -> f (y + 1) = f y + log y) (hn : n != 0)
  proof: by
  refine Nat.le_induction (by simp) (fun m hm IH => ?_) n (Nat.one_le_iff_ne_zero.2 hn)
  have A : 0 < (m : Real) := Nat.cast_pos.2 hm
  simp only [hf_feq A, Nat.cast_add, Nat.cast_one, Nat.add_succ_sub_one, add_zero]
  rw [IH]; rw [add_assoc]; rw [← log_mul (Nat.cast_ne_zero.mpr (Nat.factorial_n

中文:
定理 f_nat_eq
  条件: (hf_feq : 对任意 {y : 实数}, 0 < y -> f (y + 1) = f y + log y) (hn : n != 0)
  证明: by
  refine Nat.le_induction (by simp) (fun m hm IH => ?_) n (Nat.one_le_iff_ne_zero.2 hn)
  have A : 0 < (m : Real) := Nat.cast_pos.2 hm
  simp only [hf_feq A, Nat.cast_add, Nat.cast_one, Nat.add_succ_sub_one, add_zero]
  rw [IH]; rw [add_assoc]; rw [← log_mul (Nat.cast_ne_zero.mpr (Nat.factorial_n

Depends on / 依赖: A.ne, Nat.add_succ_sub_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ne_zero.mpr, Nat.cast_one, Nat.cast_pos, Nat.factorial_ne_zero, Nat.factorial_succ, Nat.le_induction, Nat.one_le_iff_ne_zero, Nat.succ_pred_eq_of_pos, add_assoc, add_succ_sub_one, add_zero, cast_add, cast_mul, cast_ne_zero, cast_one, cast_pos
-/
theorem f_nat_eq (hf_feq : forall {y : Real}, 0 < y -> f (y + 1) = f y + log y) (hn : n != 0) :
    f n = f 1 + log (n - 1)! := by
  refine Nat.le_induction (by simp) (fun m hm IH => ?_) n (Nat.one_le_iff_ne_zero.2 hn)
  have A : 0 < (m : Real) := Nat.cast_pos.2 hm
  simp only [hf_feq A, Nat.cast_add, Nat.cast_one, Nat.add_succ_sub_one, add_zero]
  rw [IH]; rw [add_assoc]; rw [← log_mul (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) A.ne']; rw [←
    Nat.cast_mul]
  conv_rhs => rw [← Nat.succ_pred_eq_of_pos hm, Nat.factorial_succ, mul_comm]
  congr
  exact (Nat.succ_pred_eq_of_pos hm).symm

/--
theorem `f_add_nat_eq` / 定理 `f_add_nat_eq`

English:
theorem f_add_nat_eq
  given: (hf_feq : forall {y : Real}, 0 < y -> f (y + 1) = f y + log y) (hx : 0 < x) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n hn =>
    have : x + n.succ = x + n + 1 := by push_cast; ring
    rw [this]; rw [hf_feq]; rw [hn]
    · rw [Finset.range_add_one, Finset.sum_insert Finset.notMem_range_self]
      abel
    · linarith [(Nat.cast_nonneg n : 0 <= (n : Real))]

中文:
定理 f_add_nat_eq
  条件: (hf_feq : 对任意 {y : 实数}, 0 < y -> f (y + 1) = f y + log y) (hx : 0 < x) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n hn =>
    have : x + n.succ = x + n + 1 := by push_cast; ring
    rw [this]; rw [hf_feq]; rw [hn]
    · rw [Finset.range_add_one, Finset.sum_insert Finset.notMem_range_self]
      abel
    · linarith [(Nat.cast_nonneg n : 0 <= (n : Real))]

Depends on / 依赖: Finset, Finset.notMem_range_self, Finset.range_add_one, Finset.sum_insert, Nat.cast_nonneg, cast_nonneg, hf_feq, n.succ, notMem_range_self, range_add_one, sum_insert
-/
theorem f_add_nat_eq (hf_feq : forall {y : Real}, 0 < y -> f (y + 1) = f y + log y) (hx : 0 < x) (n : Nat) :
    f (x + n) = f x + ∑ m in Finset.range n, log (x + m) := by
  induction n with
  | zero => simp
  | succ n hn =>
    have : x + n.succ = x + n + 1 := by push_cast; ring
    rw [this]; rw [hf_feq]; rw [hn]
    · rw [Finset.range_add_one, Finset.sum_insert Finset.notMem_range_self]
      abel
    · linarith [(Nat.cast_nonneg n : 0 <= (n : Real))]

/--
theorem `f_add_nat_le` / 定理 `f_add_nat_le`

English:
theorem f_add_nat_le
  statement: (hf_conv : ConvexOn Real (Ioi 0) f)
  proof: by
  have hn' : 0 < (n : Real) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have : f n + x * log n = (1 - x) * f n + x * f (n + 1) := by rw [hf_feq hn']; ring
  rw [this]; rw [(by ring : (n : Real) + x = (1 - x) * n + x * (n + 1))]
  simpa only [smul_eq_mul] using
    hf_conv.2 hn' (by linarith : 0

中文:
定理 f_add_nat_le
  结论: (hf_conv : ConvexOn 实数 (Ioi 0) f)
  证明: by
  have hn' : 0 < (n : Real) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have : f n + x * log n = (1 - x) * f n + x * f (n + 1) := by rw [hf_feq hn']; ring
  rw [this]; rw [(by ring : (n : Real) + x = (1 - x) * n + x * (n + 1))]
  simpa only [smul_eq_mul] using
    hf_conv.2 hn' (by linarith : 0

Depends on / 依赖: Nat.cast_pos.mpr, Nat.pos_of_ne_zero, cast_pos, hf_conv, hf_feq, hx.le, pos_of_ne_zero, smul_eq_mul
-/
theorem f_add_nat_le (hf_conv : ConvexOn Real (Ioi 0) f)
    (hf_feq : forall {y : Real}, 0 < y -> f (y + 1) = f y + log y) (hn : n != 0) (hx : 0 < x) (hx' : x <= 1) :
    f (n + x) <= f n + x * log n := by
  have hn' : 0 < (n : Real) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have : f n + x * log n = (1 - x) * f n + x * f (n + 1) := by rw [hf_feq hn']; ring
  rw [this]; rw [(by ring : (n : Real) + x = (1 - x) * n + x * (n + 1))]
  simpa only [smul_eq_mul] using
    hf_conv.2 hn' (by linarith : 0 < (n + 1 : Real)) (by linarith : 0 <= 1 - x) hx.le (by linarith)

/--
theorem `f_add_nat_ge` / 定理 `f_add_nat_ge`

English:
theorem f_add_nat_ge
  statement: (hf_conv : ConvexOn Real (Ioi 0) f)
  proof: by
  have npos : 0 < (n : Real) - 1 := by rw [← Nat.cast_one, sub_pos, Nat.cast_lt]; lia
  have c :=
    (convexOn_iff_slope_mono_adjacent.mp <| hf_conv).2 npos (by linarith : 0 < (n : Real) + x)
      (by linarith : (n : Real) - 1 < (n : Real)) (by linarith)
  rw [add_sub_cancel_left]; rw [sub_sub_

中文:
定理 f_add_nat_ge
  结论: (hf_conv : ConvexOn 实数 (Ioi 0) f)
  证明: by
  have npos : 0 < (n : Real) - 1 := by rw [← Nat.cast_one, sub_pos, Nat.cast_lt]; lia
  have c :=
    (convexOn_iff_slope_mono_adjacent.mp <| hf_conv).2 npos (by linarith : 0 < (n : Real) + x)
      (by linarith : (n : Real) - 1 < (n : Real)) (by linarith)
  rw [add_sub_cancel_left]; rw [sub_sub_

Depends on / 依赖: Nat.cast_lt, Nat.cast_one, add_, add_sub_cancel_left, cast_lt, cast_one, convexOn_iff_slope_mono_adjacent, convexOn_iff_slope_mono_adjacent.mp, div_one, eq_sub_iff_add_eq, hf_conv, hf_feq, le_sub_iff_add_le, mul_comm, sub_add_cancel, sub_pos, sub_sub_cancel
-/
theorem f_add_nat_ge (hf_conv : ConvexOn Real (Ioi 0) f)
    (hf_feq : forall {y : Real}, 0 < y -> f (y + 1) = f y + log y) (hn : 2 <= n) (hx : 0 < x) :
    f n + x * log (n - 1) <= f (n + x) := by
  have npos : 0 < (n : Real) - 1 := by rw [← Nat.cast_one, sub_pos, Nat.cast_lt]; lia
  have c :=
    (convexOn_iff_slope_mono_adjacent.mp <| hf_conv).2 npos (by linarith : 0 < (n : Real) + x)
      (by linarith : (n : Real) - 1 < (n : Real)) (by linarith)
  rw [add_sub_cancel_left]; rw [sub_sub_cancel]; rw [div_one] at c
  have : f (↑n - 1) = f n - log (↑n - 1) := by
    rw [eq_sub_iff_add_eq]; rw [← hf_feq npos]; rw [sub_add_cancel]
  rwa [this, le_div_iff₀ hx, sub_sub_cancel, le_sub_iff_add_le, mul_comm _ x, add_comm] at c

/--
theorem `logGammaSeq_add_one` / 定理 `logGammaSeq_add_one`

English:
theorem logGammaSeq_add_one
  given: (x : Real) (n : Nat)
  proof: by
  dsimp only [Nat.factorial_succ, logGammaSeq]
  conv_rhs => rw [Finset.sum_range_succ', Nat.cast_zero, add_zero]
  rw [Nat.cast_mul]; rw [log_mul]; rotate_left
  · rw [Nat.cast_ne_zero]; exact Nat.succ_ne_zero n
  · rw [Nat.cast_ne_zero]; exact Nat.factorial_ne_zero n
  have :
    ∑ m in Finset.

中文:
定理 logGammaSeq_add_one
  条件: (x : 实数) (n : 自然数)
  证明: by
  dsimp only [Nat.factorial_succ, logGammaSeq]
  conv_rhs => rw [Finset.sum_range_succ', Nat.cast_zero, add_zero]
  rw [Nat.cast_mul]; rw [log_mul]; rotate_left
  · rw [Nat.cast_ne_zero]; exact Nat.succ_ne_zero n
  · rw [Nat.cast_ne_zero]; exact Nat.factorial_ne_zero n
  have :
    ∑ m in Finset.

Depends on / 依赖: F.IsEquivalence, Finset, Finset.range, Finset.sum_range_succ, IsEquivalence, Nat.cast_add_one, Nat.cast_mul, Nat.cast_ne_zero, Nat.cast_zero, Nat.factorial_ne_zero, Nat.factorial_succ, Nat.succ_ne_zero, add_zero, cast_add_one, cast_mul, cast_ne_zero, cast_zero, conv_rhs, factorial_ne_zero, factorial_succ
-/
theorem logGammaSeq_add_one (x : Real) (n : Nat) :
    logGammaSeq (x + 1) n = logGammaSeq x (n + 1) + log x - (x + 1) * (log (n + 1) - log n) := by
  dsimp only [Nat.factorial_succ, logGammaSeq]
  conv_rhs => rw [Finset.sum_range_succ', Nat.cast_zero, add_zero]
  rw [Nat.cast_mul]; rw [log_mul]; rotate_left
  · rw [Nat.cast_ne_zero]; exact Nat.succ_ne_zero n
  · rw [Nat.cast_ne_zero]; exact Nat.factorial_ne_zero n
  have :
    ∑ m in Finset.range (n + 1), log (x + 1 + ↑m) =
      ∑ k in Finset.range (n + 1), log (x + ↑(k + 1)) := by
    congr! 2 with m
    push_cast
    abel
  rw [← this]; rw [Nat.cast_add_one n]
  ring

/--
theorem `le_logGammaSeq` / 定理 `le_logGammaSeq`

English:
theorem le_logGammaSeq
  statement: (hf_conv : ConvexOn Real (Ioi 0) f)
  proof: by
  rw [logGammaSeq]; rw [← add_sub_assoc]; rw [le_sub_iff_add_le]; rw [← f_add_nat_eq (@hf_feq) hx]; rw [add_comm x]
  refine (f_add_nat_le hf_conv (@hf_feq) (Nat.add_one_ne_zero n) hx hx').trans (le_of_eq ?_)
  rw [f_nat_eq @hf_feq (by lia : n + 1 != 0)]; rw [Nat.add_sub_cancel]; rw [Nat.cast_add

中文:
定理 le_logGammaSeq
  结论: (hf_conv : ConvexOn 实数 (Ioi 0) f)
  证明: by
  rw [logGammaSeq]; rw [← add_sub_assoc]; rw [le_sub_iff_add_le]; rw [← f_add_nat_eq (@hf_feq) hx]; rw [add_comm x]
  refine (f_add_nat_le hf_conv (@hf_feq) (Nat.add_one_ne_zero n) hx hx').trans (le_of_eq ?_)
  rw [f_nat_eq @hf_feq (by lia : n + 1 != 0)]; rw [Nat.add_sub_cancel]; rw [Nat.cast_add

Depends on / 依赖: Nat.add_one_ne_zero, Nat.add_sub_cancel, Nat.cast_add_one, add_comm, add_one_ne_zero, add_sub_assoc, add_sub_cancel, cast_add_one, f_add_nat_eq, f_add_nat_le, f_nat_eq, hf_conv, hf_feq, le_of_eq, le_sub_iff_add_le, logGammaSeq
-/
theorem le_logGammaSeq (hf_conv : ConvexOn Real (Ioi 0) f)
    (hf_feq : forall {y : Real}, 0 < y -> f (y + 1) = f y + log y) (hx : 0 < x) (hx' : x <= 1) (n : Nat) :
    f x <= f 1 + x * log (n + 1) - x * log n + logGammaSeq x n := by
  rw [logGammaSeq]; rw [← add_sub_assoc]; rw [le_sub_iff_add_le]; rw [← f_add_nat_eq (@hf_feq) hx]; rw [add_comm x]
  refine (f_add_nat_le hf_conv (@hf_feq) (Nat.add_one_ne_zero n) hx hx').trans (le_of_eq ?_)
  rw [f_nat_eq @hf_feq (by lia : n + 1 != 0)]; rw [Nat.add_sub_cancel]; rw [Nat.cast_add_one]
  ring

/--
theorem `ge_logGammaSeq` / 定理 `ge_logGammaSeq`

English:
theorem ge_logGammaSeq
  statement: (hf_conv : ConvexOn Real (Ioi 0) f)
  proof: by
  dsimp [logGammaSeq]
  rw [← add_sub_assoc]; rw [sub_le_iff_le_add]; rw [← f_add_nat_eq (@hf_feq) hx]; rw [add_comm x _]
  refine le_trans (le_of_eq ?_) (f_add_nat_ge hf_conv @hf_feq ?_ hx)
  · rw [f_nat_eq @hf_feq, Nat.add_sub_cancel, Nat.cast_add_one, add_sub_cancel_right]
    · ring
    · exa

中文:
定理 ge_logGammaSeq
  结论: (hf_conv : ConvexOn 实数 (Ioi 0) f)
  证明: by
  dsimp [logGammaSeq]
  rw [← add_sub_assoc]; rw [sub_le_iff_le_add]; rw [← f_add_nat_eq (@hf_feq) hx]; rw [add_comm x _]
  refine le_trans (le_of_eq ?_) (f_add_nat_ge hf_conv @hf_feq ?_ hx)
  · rw [f_nat_eq @hf_feq, Nat.add_sub_cancel, Nat.cast_add_one, add_sub_cancel_right]
    · ring
    · exa

Depends on / 依赖: Nat.add_sub_cancel, Nat.cast_add_one, Nat.succ_ne_zero, add_comm, add_sub_assoc, add_sub_cancel, add_sub_cancel_right, cast_add_one, f_add_nat_eq, f_add_nat_ge, f_nat_eq, hf_conv, hf_feq, le_of_eq, le_trans, logGammaSeq, sub_le_iff_le_add, succ_ne_zero
-/
theorem ge_logGammaSeq (hf_conv : ConvexOn Real (Ioi 0) f)
    (hf_feq : forall {y : Real}, 0 < y -> f (y + 1) = f y + log y) (hx : 0 < x) (hn : n != 0) :
    f 1 + logGammaSeq x n <= f x := by
  dsimp [logGammaSeq]
  rw [← add_sub_assoc]; rw [sub_le_iff_le_add]; rw [← f_add_nat_eq (@hf_feq) hx]; rw [add_comm x _]
  refine le_trans (le_of_eq ?_) (f_add_nat_ge hf_conv @hf_feq ?_ hx)
  · rw [f_nat_eq @hf_feq, Nat.add_sub_cancel, Nat.cast_add_one, add_sub_cancel_right]
    · ring
    · exact Nat.succ_ne_zero _
  · lia

/--
theorem `tendsto_logGammaSeq_of_le_one` / 定理 `tendsto_logGammaSeq_of_le_one`

English:
theorem tendsto_logGammaSeq_of_le_one
  statement: (hf_conv : ConvexOn Real (Ioi 0) f)
  proof: by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := logGammaSeq x)
    (g := fun n => f x - f 1 - x * (log (n + 1) - log n)) ?_ tendsto_const_nhds ?_ ?_
  · have : f x - f 1 = f x - f 1 - x * 0 := by ring
    nth_rw 2 [this]
    exact Tendsto.sub tendsto_const_nhds (tendsto_log_nat_add_one_

中文:
定理 tendsto_logGammaSeq_of_le_one
  结论: (hf_conv : ConvexOn 实数 (Ioi 0) f)
  证明: by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := logGammaSeq x)
    (g := fun n => f x - f 1 - x * (log (n + 1) - log n)) ?_ tendsto_const_nhds ?_ ?_
  · have : f x - f 1 = f x - f 1 - x * 0 := by ring
    nth_rw 2 [this]
    exact Tendsto.sub tendsto_const_nhds (tendsto_log_nat_add_one_

Depends on / 依赖: Tendsto, Tendsto.sub, const_mul, convert, filter_upwards, hf_conv, hf_feq, le_logGammaSeq, logGammaSeq, nth_rw, sub_le_iff_le_add, tendsto_const_nhds, tendsto_log_nat_add_one_sub_log, tendsto_log_nat_add_one_sub_log.const_mul, tendsto_of_tendsto_of_tendsto_of_le_of_le
-/
theorem tendsto_logGammaSeq_of_le_one (hf_conv : ConvexOn Real (Ioi 0) f)
    (hf_feq : forall {y : Real}, 0 < y -> f (y + 1) = f y + log y) (hx : 0 < x) (hx' : x <= 1) :
    Tendsto (logGammaSeq x) atTop (𝓝 <| f x - f 1) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (f := logGammaSeq x)
    (g := fun n => f x - f 1 - x * (log (n + 1) - log n)) ?_ tendsto_const_nhds ?_ ?_
  · have : f x - f 1 = f x - f 1 - x * 0 := by ring
    nth_rw 2 [this]
    exact Tendsto.sub tendsto_const_nhds (tendsto_log_nat_add_one_sub_log.const_mul _)
  · filter_upwards with n
    rw [sub_le_iff_le_add']; rw [sub_le_iff_le_add']
    convert! le_logGammaSeq hf_conv (@hf_feq) hx hx' n using 1
    ring
  · change forallᶠ n : Nat in atTop, logGammaSeq x n <= f x - f 1
    filter_upwards [eventually_ne_atTop 0] with n hn using
      le_sub_iff_add_le'.mpr (ge_logGammaSeq hf_conv hf_feq hx hn)

/--
theorem `tendsto_logGammaSeq` / 定理 `tendsto_logGammaSeq`

English:
theorem tendsto_logGammaSeq
  statement: (hf_conv : ConvexOn Real (Ioi 0) f)
  proof: by
  suffices forall m : Nat, ↑m < x -> x <= m + 1 -> Tendsto (logGammaSeq x) atTop (𝓝 <| f x - f 1) by
    refine this ⌈x - 1⌉₊ ?_ ?_
    · rcases lt_or_ge x 1 with ⟨⟩
      · rwa [Nat.ceil_eq_zero.mpr (by linarith : x - 1 <= 0), Nat.cast_zero]
      · convert! Nat.ceil_lt_add_one (by linarith : 0 

中文:
定理 tendsto_logGammaSeq
  结论: (hf_conv : ConvexOn 实数 (Ioi 0) f)
  证明: by
  suffices forall m : Nat, ↑m < x -> x <= m + 1 -> Tendsto (logGammaSeq x) atTop (𝓝 <| f x - f 1) by
    refine this ⌈x - 1⌉₊ ?_ ?_
    · rcases lt_or_ge x 1 with ⟨⟩
      · rwa [Nat.ceil_eq_zero.mpr (by linarith : x - 1 <= 0), Nat.cast_zero]
      · convert! Nat.ceil_lt_add_one (by linarith : 0 

Depends on / 依赖: Nat.cast_zero, Nat.ceil_eq_zero.mpr, Nat.ceil_lt_add_one, Nat.le_ceil, Tendsto, cast_zero, ceil_eq_zero, ceil_lt_add_one, convert, generalizing, hf_conv, hf_feq, le_ceil, logGammaSeq, lt_or_ge, sub_le_iff_le_add, tendsto_logGammaSeq_of_le_one, zero_add
-/
theorem tendsto_logGammaSeq (hf_conv : ConvexOn Real (Ioi 0) f)
    (hf_feq : forall {y : Real}, 0 < y -> f (y + 1) = f y + log y) (hx : 0 < x) :
    Tendsto (logGammaSeq x) atTop (𝓝 <| f x - f 1) := by
  suffices forall m : Nat, ↑m < x -> x <= m + 1 -> Tendsto (logGammaSeq x) atTop (𝓝 <| f x - f 1) by
    refine this ⌈x - 1⌉₊ ?_ ?_
    · rcases lt_or_ge x 1 with ⟨⟩
      · rwa [Nat.ceil_eq_zero.mpr (by linarith : x - 1 <= 0), Nat.cast_zero]
      · convert! Nat.ceil_lt_add_one (by linarith : 0 <= x - 1)
        abel
    · rw [← sub_le_iff_le_add]; exact Nat.le_ceil _
  intro m
  induction m generalizing x with
  | zero =>
    rw [Nat.cast_zero]; rw [zero_add]
    exact fun _ hx' => tendsto_logGammaSeq_of_le_one hf_conv (@hf_feq) hx hx'
  | succ m hm =>
    intro hy hy'
    rw [Nat.cast_succ]; rw [← sub_le_iff_le_add] at hy'
    rw [Nat.cast_succ]; rw [← lt_sub_iff_add_lt] at hy
    specialize hm ((Nat.cast_nonneg _).trans_lt hy) hy hy'
    -- now massage gauss_product n (x - 1) into gauss_product (n - 1) x
    have :
      forallᶠ n : Nat in atTop,
        logGammaSeq (x - 1) n =
          logGammaSeq x (n - 1) + x * (log (↑(n - 1) + 1) - log ↑(n - 1)) - log (x - 1) := by
      refine Eventually.mp (eventually_ge_atTop 1) (Eventually.of_forall fun n hn => ?_)
      have := logGammaSeq_add_one (x - 1) (n - 1)
      rw [sub_add_cancel]; rw [Nat.sub_add_cancel hn] at this
      rw [this]
      ring
    replace hm :=
      ((Tendsto.congr' this hm).add (tendsto_const_nhds : Tendsto (fun _ => log (x - 1)) _ _)).comp
        (tendsto_add_atTop_nat 1)
    have :
      ((fun x_1 : Nat =>
            (fun n : Nat =>
                  logGammaSeq x (n - 1) + x * (log (↑(n - 1) + 1) - log ↑(n - 1)) - log (x - 1))
                x_1 +
              (fun b : Nat => log (x - 1)) x_1) ∘
          fun a : Nat => a + 1) =
        fun n => logGammaSeq x n + x * (log (↑n + 1) - log ↑n) := by
      ext1 n
      dsimp only [Function.comp_apply]
      rw [sub_add_cancel]; rw [Nat.add_sub_cancel]
    rw [this] at hm
    convert! hm.sub (tendsto_log_nat_add_one_sub_log.const_mul x) using 2
    · ring
    · have := hf_feq ((Nat.cast_nonneg m).trans_lt hy)
      rw [sub_add_cancel] at this
      rw [this]
      ring

/--
theorem `tendsto_log_gamma` / 定理 `tendsto_log_gamma`

English:
theorem tendsto_log_gamma
  given: {x : Real} (hx : 0 < x)
  proof: by
  have : log (Gamma x) = (log ∘ Gamma) x - (log ∘ Gamma) 1 := by
    simp_rw [Function.comp_apply, Gamma_one, log_one, sub_zero]
  rw [this]
  refine BohrMollerup.tendsto_logGammaSeq convexOn_log_Gamma (fun {y} hy => ?_) hx
  rw [Function.comp_apply]; rw [Gamma_add_one hy.ne']; rw [log_mul hy.ne'

中文:
定理 tendsto_log_gamma
  条件: {x : 实数} (hx : 0 < x)
  证明: by
  have : log (Gamma x) = (log ∘ Gamma) x - (log ∘ Gamma) 1 := by
    simp_rw [Function.comp_apply, Gamma_one, log_one, sub_zero]
  rw [this]
  refine BohrMollerup.tendsto_logGammaSeq convexOn_log_Gamma (fun {y} hy => ?_) hx
  rw [Function.comp_apply]; rw [Gamma_add_one hy.ne']; rw [log_mul hy.ne'

Depends on / 依赖: BohrMollerup, BohrMollerup.tendsto_logGammaSeq, Function, Function.comp_apply, Gamma_add_one, Gamma_one, Gamma_pos_of_pos, add_comm, comp_apply, convexOn_log_Gamma, hy.ne, log_mul, log_one, simp_rw, sub_zero, tendsto_logGammaSeq
-/
theorem tendsto_log_gamma {x : Real} (hx : 0 < x) :
    Tendsto (logGammaSeq x) atTop (𝓝 <| log (Gamma x)) := by
  have : log (Gamma x) = (log ∘ Gamma) x - (log ∘ Gamma) 1 := by
    simp_rw [Function.comp_apply, Gamma_one, log_one, sub_zero]
  rw [this]
  refine BohrMollerup.tendsto_logGammaSeq convexOn_log_Gamma (fun {y} hy => ?_) hx
  rw [Function.comp_apply]; rw [Gamma_add_one hy.ne']; rw [log_mul hy.ne' (Gamma_pos_of_pos hy).ne']; rw [add_comm]; rw [Function.comp_apply]

end BohrMollerup

-- (namespace)
/--
theorem `eq_Gamma_of_log_convex` / 定理 `eq_Gamma_of_log_convex`

English:
theorem eq_Gamma_of_log_convex
  statement: {f : Real -> Real} (hf_conv : ConvexOn Real (Ioi 0) (log ∘ f))
  proof: by
  suffices EqOn (log ∘ f) (log ∘ Gamma) (Ioi (0 : Real)) from
    fun x hx => log_injOn_pos (hf_pos hx) (Gamma_pos_of_pos hx) (this hx)
  intro x hx
  have e1 := BohrMollerup.tendsto_logGammaSeq hf_conv ?_ hx
  · rw [Function.comp_apply (f := log) (g := f) (x := 1), hf_one, log_one, sub_zero] at 

中文:
定理 eq_Gamma_of_log_convex
  结论: {f : 实数 -> 实数} (hf_conv : ConvexOn 实数 (Ioi 0) (log ∘ f))
  证明: by
  suffices EqOn (log ∘ f) (log ∘ Gamma) (Ioi (0 : Real)) from
    fun x hx => log_injOn_pos (hf_pos hx) (Gamma_pos_of_pos hx) (this hx)
  intro x hx
  have e1 := BohrMollerup.tendsto_logGammaSeq hf_conv ?_ hx
  · rw [Function.comp_apply (f := log) (g := f) (x := 1), hf_one, log_one, sub_zero] at 

Depends on / 依赖: BohrMollerup, BohrMollerup.tendsto_logGammaSeq, BohrMollerup.tendsto_log_gamma, Function, Function.comp_apply, Gamma_pos_of_pos, comp_apply, hf_conv, hf_feq, hf_one, hf_pos, hy.ne, log_injOn_pos, log_mul, log_one, sub_zero, tendsto_logGammaSeq, tendsto_log_gamma, tendsto_nhds_unique
-/
theorem eq_Gamma_of_log_convex {f : Real -> Real} (hf_conv : ConvexOn Real (Ioi 0) (log ∘ f))
    (hf_feq : forall {y : Real}, 0 < y -> f (y + 1) = y * f y) (hf_pos : forall {y : Real}, 0 < y -> 0 < f y)
    (hf_one : f 1 = 1) : EqOn f Gamma (Ioi (0 : Real)) := by
  suffices EqOn (log ∘ f) (log ∘ Gamma) (Ioi (0 : Real)) from
    fun x hx => log_injOn_pos (hf_pos hx) (Gamma_pos_of_pos hx) (this hx)
  intro x hx
  have e1 := BohrMollerup.tendsto_logGammaSeq hf_conv ?_ hx
  · rw [Function.comp_apply (f := log) (g := f) (x := 1), hf_one, log_one, sub_zero] at e1
    exact tendsto_nhds_unique e1 (BohrMollerup.tendsto_log_gamma hx)
  · intro y hy
    rw [Function.comp_apply]; rw [Function.comp_apply]; rw [hf_feq hy]; rw [log_mul hy.ne' (hf_pos hy).ne']
    ring

end BohrMollerup

-- (section)
section StrictMono

/--
theorem `Gamma_two` / 定理 `Gamma_two`

English:
theorem Gamma_two
  statement: Gamma 2 = 1
  proof: by simp [Nat.factorial_one]

中文:
定理 Gamma_two
  结论: Gamma 2 = 1
  证明: by simp [Nat.factorial_one]

Depends on / 依赖: Nat.factorial_one, factorial_one
-/
theorem Gamma_two : Gamma 2 = 1 := by simp [Nat.factorial_one]

/--
theorem `Gamma_three_div_two_lt_one` / 定理 `Gamma_three_div_two_lt_one`

English:
theorem Gamma_three_div_two_lt_one
  statement: Gamma (3 / 2) < 1
  proof: by
  -- This can also be proved using the closed-form evaluation of `Gamma (1 / 2)` in
  -- `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`, but we give a
  -- self-contained proof using log-convexity to avoid unnecessary imports.
  have A : (0 : Real) < 3 / 2 := by simp
  have :=

中文:
定理 Gamma_three_div_two_lt_one
  结论: Gamma (3 / 2) < 1
  证明: by
  -- This can also be proved using the closed-form evaluation of `Gamma (1 / 2)` in
  -- `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`, but we give a
  -- self-contained proof using log-convexity to avoid unnecessary imports.
  have A : (0 : Real) < 3 / 2 := by simp
  have :=
-/
theorem Gamma_three_div_two_lt_one : Gamma (3 / 2) < 1 := by
  -- This can also be proved using the closed-form evaluation of `Gamma (1 / 2)` in
  -- `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`, but we give a
  -- self-contained proof using log-convexity to avoid unnecessary imports.
  have A : (0 : Real) < 3 / 2 := by simp
  have :=
    BohrMollerup.f_add_nat_le convexOn_log_Gamma (fun {y} hy => ?_) two_ne_zero one_half_pos
      (by norm_num : 1 / 2 <= (1 : Real))
  swap
  · rw [Function.comp_apply, Gamma_add_one hy.ne', log_mul hy.ne' (Gamma_pos_of_pos hy).ne',
      add_comm, Function.comp_apply]
  rw [Function.comp_apply]; rw [Function.comp_apply]; rw [Nat.cast_two]; rw [Gamma_two]; rw [log_one]; rw [zero_add]; rw [(by norm_num : (2 : Real) + 1 / 2 = 3 / 2 + 1)]; rw [Gamma_add_one A.ne']; rw [log_mul A.ne' (Gamma_pos_of_pos A).ne']; rw [← le_sub_iff_add_le']; rw [log_le_iff_le_exp (Gamma_pos_of_pos A)] at this
  refine this.trans_lt (exp_lt_one_iff.mpr ?_)
  rw [mul_comm]; rw [← mul_div_assoc]; rw [div_sub' two_ne_zero]
  refine div_neg_of_neg_of_pos ?_ two_pos
  rw [sub_neg]; rw [mul_one]; rw [← Nat.cast_two]; rw [← log_pow]; rw [← exp_lt_exp]; rw [Nat.cast_two]; rw [exp_log two_pos]; rw [exp_log] <;>
    norm_num

/--
theorem `Gamma_strictAntiOn_Ioc` / 定理 `Gamma_strictAntiOn_Ioc`

English:
theorem Gamma_strictAntiOn_Ioc
  statement: StrictAntiOn Gamma (Ioc 0 1)
  proof: convexOn_Gamma.strictAntiOn (by simp) (by norm_num)
    Gamma_one.symm ▸ Gamma_three_div_two_lt_one

中文:
定理 Gamma_strictAntiOn_Ioc
  结论: StrictAntiOn Gamma (Ioc 0 1)
  证明: convexOn_Gamma.strictAntiOn (by simp) (by norm_num)
    Gamma_one.symm ▸ Gamma_three_div_two_lt_one

Depends on / 依赖: Gamma_one, Gamma_one.symm, Gamma_three_div_two_lt_one, convexOn_Gamma, convexOn_Gamma.strictAntiOn, strictAntiOn
-/
theorem Gamma_strictAntiOn_Ioc : StrictAntiOn Gamma (Ioc 0 1) :=
convexOn_Gamma.strictAntiOn (by simp) (by norm_num)
    Gamma_one.symm ▸ Gamma_three_div_two_lt_one

/--
theorem `Gamma_strictMonoOn_Ici` / 定理 `Gamma_strictMonoOn_Ici`

English:
theorem Gamma_strictMonoOn_Ici
  statement: StrictMonoOn Gamma (Ici 2)
  proof: by
  convert!
    convexOn_Gamma.strictMonoOn (by simp : (0 : Real) < 3 / 2) (by norm_num : (3 / 2 : Real) < 2)
      (Gamma_two.symm ▸ Gamma_three_div_two_lt_one)
  symm
  rw [inter_eq_right]
exact fun x hx => two_pos.trans_le mem_Ici.mp hx

中文:
定理 Gamma_strictMonoOn_Ici
  结论: StrictMonoOn Gamma (Ici 2)
  证明: by
  convert!
    convexOn_Gamma.strictMonoOn (by simp : (0 : Real) < 3 / 2) (by norm_num : (3 / 2 : Real) < 2)
      (Gamma_two.symm ▸ Gamma_three_div_two_lt_one)
  symm
  rw [inter_eq_right]
exact fun x hx => two_pos.trans_le mem_Ici.mp hx

Depends on / 依赖: Gamma_three_div_two_lt_one, Gamma_two, Gamma_two.symm, convert, convexOn_Gamma, convexOn_Gamma.strictMonoOn, inter_eq_right, mem_Ici, mem_Ici.mp, strictMonoOn, trans_le, two_pos, two_pos.trans_le
-/
theorem Gamma_strictMonoOn_Ici : StrictMonoOn Gamma (Ici 2) := by
  convert!
    convexOn_Gamma.strictMonoOn (by simp : (0 : Real) < 3 / 2) (by norm_num : (3 / 2 : Real) < 2)
      (Gamma_two.symm ▸ Gamma_three_div_two_lt_one)
  symm
  rw [inter_eq_right]
exact fun x hx => two_pos.trans_le mem_Ici.mp hx

-- TODO: prove uniqueness once the necessary material to do so makes its way into Mathlib
/--
theorem `exists_isMinOn_Gamma_Ioi` / 定理 `exists_isMinOn_Gamma_Ioi`

English:
theorem exists_isMinOn_Gamma_Ioi
  statement: exists x in Ioo 1 2, IsMinOn Gamma (Ioi 0) x
  proof: by
have ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr one_le_two)
differentiableOn_Gamma_Ioi.continuousOn.mono by grind
  have ⟨h1, h2, h3half⟩ : Γ (3 / 2) < Γ 1 ∧ Γ (3 / 2) < Γ 2 ∧ Γ x <= Γ (3 / 2) := by
simpa [Gamma_three_div_two_lt_one] using hmin by norm_num
  refine ⟨x, by gri

中文:
定理 exists_isMinOn_Gamma_Ioi
  结论: 存在 x in Ioo 1 2, IsMinOn Gamma (Ioi 0) x
  证明: by
have ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr one_le_two)
differentiableOn_Gamma_Ioi.continuousOn.mono by grind
  have ⟨h1, h2, h3half⟩ : Γ (3 / 2) < Γ 1 ∧ Γ (3 / 2) < Γ 2 ∧ Γ x <= Γ (3 / 2) := by
simpa [Gamma_three_div_two_lt_one] using hmin by norm_num
  refine ⟨x, by gri

Depends on / 依赖: Gamma_strictAntiOn_Ioc, Gamma_strictAntiOn_Ioc.antitoneOn, Gamma_three_div_two_lt_one, antitoneOn, continuousOn, differentiableOn_Gamma_Ioi, differentiableOn_Gamma_Ioi.continuousOn.mono, exists_isMinOn, h1.le, h3half, h3half.trans, hy.right, isCompact_Icc, isCompact_Icc.exists_isMinOn, nonempty_Icc, nonempty_Icc.mpr, one_le_two
-/
theorem exists_isMinOn_Gamma_Ioi : exists x in Ioo 1 2, IsMinOn Gamma (Ioi 0) x := by
have ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr one_le_two)
differentiableOn_Gamma_Ioi.continuousOn.mono by grind
  have ⟨h1, h2, h3half⟩ : Γ (3 / 2) < Γ 1 ∧ Γ (3 / 2) < Γ 2 ∧ Γ x <= Γ (3 / 2) := by
simpa [Gamma_three_div_two_lt_one] using hmin by norm_num
  refine ⟨x, by grind, fun y _ => ?_⟩
  obtain hy | hy | hy : y in Ioc 0 1 ∨ y in Icc 1 2 ∨ y in Ici 2 := by grind
.trans Gamma_strictAntiOn_Ioc.antitoneOn hy (by simp) hy.right · exact h3half.trans h1.le
  · exact hmin hy
.trans Gamma_strictMonoOn_Ici.monotoneOn (by simp) hy hy · exact h3half.trans h2.le

end StrictMono

section Doubling

/-!
## The Gamma doubling formula

As a fun application of the Bohr-Mollerup theorem, we prove the Gamma-function doubling formula
(for positive real `s`). The idea is that `2 ^ s * Gamma (s / 2) * Gamma (s / 2 + 1 / 2)` is
log-convex and satisfies the Gamma functional equation, so it must actually be a constant
multiple of `Gamma`, and we can compute the constant by specialising at `s = 1`. -/


/--
Definition of `doublingGamma` / `doublingGamma` 的定义

English:
definition doublingGamma
  signature: (s : Real)
  body: Gamma (s / 2) * Gamma (s / 2 + 1 / 2) * 2 ^ (s - 1) / √π

中文:
定义 doublingGamma
  签名: (s : 实数)
  定义体: Gamma (s / 2) * Gamma (s / 2 + 1 / 2) * 2 ^ (s - 1) / √π
-/
def doublingGamma (s : Real) : Real :=
  Gamma (s / 2) * Gamma (s / 2 + 1 / 2) * 2 ^ (s - 1) / √π

/--
theorem `doublingGamma_add_one` / 定理 `doublingGamma_add_one`

English:
theorem doublingGamma_add_one
  given: (s : Real) (hs : s != 0)
  proof: by
  rw [doublingGamma]; rw [doublingGamma]; rw [(by abel : s + 1 - 1 = s - 1 + 1)]; rw [add_div]; rw [add_assoc]; rw [add_halves (1 : Real)]; rw [Gamma_add_one (div_ne_zero hs two_ne_zero)]; rw [rpow_add two_pos]; rw [rpow_one]
  ring

中文:
定理 doublingGamma_add_one
  条件: (s : 实数) (hs : s != 0)
  证明: by
  rw [doublingGamma]; rw [doublingGamma]; rw [(by abel : s + 1 - 1 = s - 1 + 1)]; rw [add_div]; rw [add_assoc]; rw [add_halves (1 : Real)]; rw [Gamma_add_one (div_ne_zero hs two_ne_zero)]; rw [rpow_add two_pos]; rw [rpow_one]
  ring

Depends on / 依赖: Gamma_add_one, add_assoc, add_div, add_halves, div_ne_zero, doublingGamma, rpow_add, rpow_one, two_ne_zero, two_pos
-/
theorem doublingGamma_add_one (s : Real) (hs : s != 0) :
    doublingGamma (s + 1) = s * doublingGamma s := by
  rw [doublingGamma]; rw [doublingGamma]; rw [(by abel : s + 1 - 1 = s - 1 + 1)]; rw [add_div]; rw [add_assoc]; rw [add_halves (1 : Real)]; rw [Gamma_add_one (div_ne_zero hs two_ne_zero)]; rw [rpow_add two_pos]; rw [rpow_one]
  ring

/--
theorem `doublingGamma_one` / 定理 `doublingGamma_one`

English:
theorem doublingGamma_one
  statement: doublingGamma 1 = 1
  proof: by
  simp_rw [doublingGamma, Gamma_one_half_eq, add_halves (1 : Real), sub_self, Gamma_one, mul_one,
    rpow_zero, mul_one, div_self (sqrt_ne_zero'.mpr pi_pos)]

中文:
定理 doublingGamma_one
  结论: doublingGamma 1 = 1
  证明: by
  simp_rw [doublingGamma, Gamma_one_half_eq, add_halves (1 : Real), sub_self, Gamma_one, mul_one,
    rpow_zero, mul_one, div_self (sqrt_ne_zero'.mpr pi_pos)]

Depends on / 依赖: Gamma_one, Gamma_one_half_eq, add_halves, div_self, doublingGamma, mul_one, pi_pos, rpow_zero, simp_rw, sqrt_ne_zero, sub_self
-/
theorem doublingGamma_one : doublingGamma 1 = 1 := by
  simp_rw [doublingGamma, Gamma_one_half_eq, add_halves (1 : Real), sub_self, Gamma_one, mul_one,
    rpow_zero, mul_one, div_self (sqrt_ne_zero'.mpr pi_pos)]

/--
theorem `log_doublingGamma_eq` / 定理 `log_doublingGamma_eq`

English:
theorem log_doublingGamma_eq
  proof: by
  intro s hs
  have h1 : √π != 0 := sqrt_ne_zero'.mpr pi_pos
  have h2 : Gamma (s / 2) != 0 := (Gamma_pos_of_pos <| div_pos hs two_pos).ne'
  have h3 : Gamma (s / 2 + 1 / 2) != 0 :=
    (Gamma_pos_of_pos <| add_pos (div_pos hs two_pos) one_half_pos).ne'
  have h4 : (2 : Real) ^ (s - 1) != 0 := (r

中文:
定理 log_doublingGamma_eq
  证明: by
  intro s hs
  have h1 : √π != 0 := sqrt_ne_zero'.mpr pi_pos
  have h2 : Gamma (s / 2) != 0 := (Gamma_pos_of_pos <| div_pos hs two_pos).ne'
  have h3 : Gamma (s / 2 + 1 / 2) != 0 :=
    (Gamma_pos_of_pos <| add_pos (div_pos hs two_pos) one_half_pos).ne'
  have h4 : (2 : Real) ^ (s - 1) != 0 := (r

Depends on / 依赖: Function, Function.comp_apply, Gamma_pos_of_pos, add_pos, comp_apply, div_pos, doublingGamma, log_div, log_mul, log_rpow, mul_ne_zero, one_half_pos, pi_pos, rpow_pos_of_pos, sqrt_ne_zero, two_pos
-/
theorem log_doublingGamma_eq :
    EqOn (log ∘ doublingGamma)
      (fun s => log (Gamma (s / 2)) + log (Gamma (s / 2 + 1 / 2)) + s * log 2 - log (2 * √π))
      (Ioi 0) := by
  intro s hs
  have h1 : √π != 0 := sqrt_ne_zero'.mpr pi_pos
  have h2 : Gamma (s / 2) != 0 := (Gamma_pos_of_pos <| div_pos hs two_pos).ne'
  have h3 : Gamma (s / 2 + 1 / 2) != 0 :=
    (Gamma_pos_of_pos <| add_pos (div_pos hs two_pos) one_half_pos).ne'
  have h4 : (2 : Real) ^ (s - 1) != 0 := (rpow_pos_of_pos two_pos _).ne'
  rw [Function.comp_apply]; rw [doublingGamma]; rw [log_div (mul_ne_zero (mul_ne_zero h2 h3) h4) h1]; rw [log_mul (mul_ne_zero h2 h3) h4]; rw [log_mul h2 h3]; rw [log_rpow two_pos]; rw [log_mul two_ne_zero h1]
  ring_nf

/--
theorem `doublingGamma_log_convex_Ioi` / 定理 `doublingGamma_log_convex_Ioi`

English:
theorem doublingGamma_log_convex_Ioi
  statement: ConvexOn Real (Ioi (0 : Real)) (log ∘ doublingGamma)
  proof: by
  refine (((ConvexOn.add ?_ ?_).add ?_).add_const _).congr log_doublingGamma_eq.symm
  · convert!
      convexOn_log_Gamma.comp_affineMap (DistribSMul.toLinearMap Real Real (1 / 2 : Real)).toAffineMap
      using 1
    · simpa only [zero_div] using! (preimage_const_mul_Ioi₀ (0 : Real) one_half_po

中文:
定理 doublingGamma_log_convex_Ioi
  结论: ConvexOn 实数 (Ioi (0 : 实数)) (log ∘ doublingGamma)
  证明: by
  refine (((ConvexOn.add ?_ ?_).add ?_).add_const _).congr log_doublingGamma_eq.symm
  · convert!
      convexOn_log_Gamma.comp_affineMap (DistribSMul.toLinearMap Real Real (1 / 2 : Real)).toAffineMap
      using 1
    · simpa only [zero_div] using! (preimage_const_mul_Ioi₀ (0 : Real) one_half_po

Depends on / 依赖: ConvexOn, ConvexOn.add, ConvexOn.subset, DistribSMul, DistribSMul.toLinearMap, DistribSMul.toLinearMap_apply, Function, Function.comp_apply, Ioi_subset_Ioi, LinearMap, LinearMap.coe_toAffineMap, add_const, coe_toAffineMap, comp_affineMap, comp_apply, convert, convexOn_log_Gamma, convexOn_log_Gamma.comp_affineMap, log_doublingGamma_eq, log_doublingGamma_eq.symm
-/
theorem doublingGamma_log_convex_Ioi : ConvexOn Real (Ioi (0 : Real)) (log ∘ doublingGamma) := by
  refine (((ConvexOn.add ?_ ?_).add ?_).add_const _).congr log_doublingGamma_eq.symm
  · convert!
      convexOn_log_Gamma.comp_affineMap (DistribSMul.toLinearMap Real Real (1 / 2 : Real)).toAffineMap
      using 1
    · simpa only [zero_div] using! (preimage_const_mul_Ioi₀ (0 : Real) one_half_pos).symm
    · ext1 x
      simp only [LinearMap.coe_toAffineMap, Function.comp_apply, DistribSMul.toLinearMap_apply]
      rw [smul_eq_mul]; rw [mul_comm]; rw [mul_one_div]
  · refine ConvexOn.subset ?_ (Ioi_subset_Ioi <| neg_one_lt_zero.le) (convex_Ioi _)
    convert!
      convexOn_log_Gamma.comp_affineMap
        ((DistribSMul.toLinearMap Real Real (1 / 2 : Real)).toAffineMap +
          AffineMap.const Real Real (1 / 2 : Real)) using 1
    · change Ioi (-1 : Real) = ((fun x : Real => x + 1 / 2) ∘ fun x : Real => (1 / 2 : Real) * x) ⁻¹' Ioi 0
      rw [preimage_comp]; rw [preimage_add_const_Ioi]; rw [zero_sub]; rw [preimage_const_mul_Ioi₀ (_ : Real) one_half_pos]; rw [neg_div]; rw [div_self (@one_half_pos Real _).ne']
    · ext1 x
      change log (Gamma (x / 2 + 1 / 2)) = log (Gamma ((1 / 2 : Real) • x + 1 / 2))
      rw [smul_eq_mul]; rw [mul_comm]; rw [mul_one_div]
  · simpa only [mul_comm _ (log _)] using!
      (convexOn_id (convex_Ioi (0 : Real))).smul (log_pos one_lt_two).le

/--
theorem `doublingGamma_eq_Gamma` / 定理 `doublingGamma_eq_Gamma`

English:
theorem doublingGamma_eq_Gamma
  given: {s : Real} (hs : 0 < s)
  statement: doublingGamma s = Gamma s
  proof: by
  refine
    eq_Gamma_of_log_convex doublingGamma_log_convex_Ioi
      (fun {y} hy => doublingGamma_add_one y hy.ne') (fun {y} hy => ?_) doublingGamma_one hs
  apply_rules [mul_pos, Gamma_pos_of_pos, add_pos, inv_pos_of_pos, rpow_pos_of_pos, two_pos,
    one_pos, sqrt_pos_of_pos pi_pos]

中文:
定理 doublingGamma_eq_Gamma
  条件: {s : 实数} (hs : 0 < s)
  结论: doublingGamma s = Gamma s
  证明: by
  refine
    eq_Gamma_of_log_convex doublingGamma_log_convex_Ioi
      (fun {y} hy => doublingGamma_add_one y hy.ne') (fun {y} hy => ?_) doublingGamma_one hs
  apply_rules [mul_pos, Gamma_pos_of_pos, add_pos, inv_pos_of_pos, rpow_pos_of_pos, two_pos,
    one_pos, sqrt_pos_of_pos pi_pos]

Depends on / 依赖: Gamma_pos_of_pos, add_pos, apply_rules, doublingGamma_add_one, doublingGamma_log_convex_Ioi, doublingGamma_one, eq_Gamma_of_log_convex, hy.ne, inv_pos_of_pos, mul_pos, one_pos, pi_pos, rpow_pos_of_pos, sqrt_pos_of_pos, two_pos
-/
theorem doublingGamma_eq_Gamma {s : Real} (hs : 0 < s) : doublingGamma s = Gamma s := by
  refine
    eq_Gamma_of_log_convex doublingGamma_log_convex_Ioi
      (fun {y} hy => doublingGamma_add_one y hy.ne') (fun {y} hy => ?_) doublingGamma_one hs
  apply_rules [mul_pos, Gamma_pos_of_pos, add_pos, inv_pos_of_pos, rpow_pos_of_pos, two_pos,
    one_pos, sqrt_pos_of_pos pi_pos]

/--
theorem `Gamma_mul_Gamma_add_half_of_pos` / 定理 `Gamma_mul_Gamma_add_half_of_pos`

English:
theorem Gamma_mul_Gamma_add_half_of_pos
  given: {s : Real} (hs : 0 < s)
  proof: by
  rw [← doublingGamma_eq_Gamma (mul_pos two_pos hs)]; rw [doublingGamma]; rw [mul_div_cancel_left₀ _ (two_ne_zero' Real)]; rw [(by abel : 1 - 2 * s = -(2 * s - 1))]; rw [rpow_neg zero_le_two]
  field

中文:
定理 Gamma_mul_Gamma_add_half_of_pos
  条件: {s : 实数} (hs : 0 < s)
  证明: by
  rw [← doublingGamma_eq_Gamma (mul_pos two_pos hs)]; rw [doublingGamma]; rw [mul_div_cancel_left₀ _ (two_ne_zero' Real)]; rw [(by abel : 1 - 2 * s = -(2 * s - 1))]; rw [rpow_neg zero_le_two]
  field

Depends on / 依赖: doublingGamma, doublingGamma_eq_Gamma, mul_pos, rpow_neg, two_ne_zero, two_pos, zero_le_two
-/
theorem Gamma_mul_Gamma_add_half_of_pos {s : Real} (hs : 0 < s) :
    Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * 2 ^ (1 - 2 * s) * √π := by
  rw [← doublingGamma_eq_Gamma (mul_pos two_pos hs)]; rw [doublingGamma]; rw [mul_div_cancel_left₀ _ (two_ne_zero' Real)]; rw [(by abel : 1 - 2 * s = -(2 * s - 1))]; rw [rpow_neg zero_le_two]
  field

end Doubling

end Real
