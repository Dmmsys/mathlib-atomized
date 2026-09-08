/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Jensen's Formula of Complex Analysis

If a function `g : ℂ → ℂ` is analytic without zero on the closed ball with center `c` and radius
`R`, then `log ‖g ·‖` is harmonic, and the mean value theorem of harmonic functions asserts that the
circle average `circleAverage (log ‖g ·‖) c R` equals `log ‖g c‖`.  Note that `g c` equals
`meromorphicTrailingCoeffAt g c` and see `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero` for the
precise statement.

Jensen's Formula, formulated in `MeromorphicOn.circleAverage_log_norm` below, generalizes this to
the setting where `g` is merely meromorphic. In that case, the `circleAverage (log ‖g ·‖) c R`
equals `log ‖meromorphicTrailingCoeffAt g c‖` plus a correction term that accounts for the zeros and
poles of `g` within the ball.
-/

public section

open Filter MeromorphicAt MeasureTheory MeromorphicOn Metric Real Set Topology
open scoped ComplexConjugate


/-!
## Preparatory Material

In preparation to the proof of Jensen's formula, compute several circle averages and reformulate
some of the terms that appear in the formula and its proof.
-/

-- Auxiliary definitition for `circleAverage_re_herglotzRieszKernel_mul_log`. Shorthand for the
-- integrand in our computations
/-
**herglotzLogIntegrand** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable def herglotzLogIntegrand (w ρ : ℂ) : ℂ → ℝ :=
  (Complex.re ∘ herglotzRieszKernel 0 w) • (Real.log ‖· - ρ‖)

-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Continuity of the
-- herglotzLogIntegrand.
/-
**continuousAt_herglotzLogIntegrand** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma continuousAt_herglotzLogIntegrand {w ρ z : ℂ} (hz_w : z ≠ w) (hz_ρ : z ≠ ρ) :
    ContinuousAt (herglotzLogIntegrand w ρ) z := by
  have : ‖z - ρ‖ ≠ 0 := by simp_all [sub_eq_zero]
  simp only [herglotzLogIntegrand, herglotzRieszKernel_fun_def, sub_zero, smul_eq_mul]
  fun_prop (disch := grind)

-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Continuity of the
-- herglotzLogIntegrand.
/-
**continuous_herglotzLogIntegrand_circle** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma continuous_herglotzLogIntegrand_circle {w ρ : ℂ} {R r : ℝ} (hρ : ‖ρ‖ = R)
    (hr_lt : r < R) (hwr : ‖w‖ < r) :
    Continuous (fun θ ↦ herglotzLogIntegrand w ρ (circleMap 0 r θ)) := by
  rw [continuous_iff_continuousAt]
  intro θ
  apply ContinuousAt.comp (continuousAt_herglotzLogIntegrand _ _) (by fun_prop)
  all_goals
    by_contra h
    grind [norm_circleMap_zero, lt_of_le_of_lt (Complex.norm_nonneg w) hwr]

open Complex in
-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Computation for the
-- boundedness required by the dominated convergence theorem, Part I.
/-
**const_mul_norm_sub_circleMap_le_norm_sub_circleMap** 是 Mathlib 中的一个引理，位于命名空间 `
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma const_mul_norm_sub_circleMap_le_norm_sub_circleMap {r₀ r R : ℝ} {ρ : ℂ} (hρ : ‖ρ‖ = R)
    (hr₀ : 0 < r₀) (hR : 0 < R) (hr₀r : r₀ ≤ r) (hrR : r ≤ R) (θ : ℝ) :
    sqrt (r₀ / R) * ‖circleMap 0 R θ - ρ‖ ≤ ‖circleMap 0 r θ - ρ‖ := by
  have h_cos_law (r₁ : ℝ) :
      ‖circleMap 0 r₁ θ - ρ‖ ^ 2 = r₁ ^ 2 + R ^ 2 - 2 * r₁ * R * Real.cos (θ - Complex.arg ρ) := by
    rw [← ofReal_inj, ← normSq_eq_norm_sq, normSq_sub ]
    suffices (circleMap 0 r₁ θ * (conj) ρ).re = r₁ * ‖ρ‖ * Real.cos (θ - ρ.arg) by
      simp [normSq_eq_norm_sq, hρ, -mul_re, this, mul_assoc]
    conv_lhs => rw [← norm_mul_exp_arg_mul_I ρ, ← circleMap_zero, conj_circleMap_zero,
      circleMap_zero_mul, circleMap_zero_re, ← sub_eq_add_neg]
  have : (r₀ / R) * ‖circleMap 0 R θ - ρ‖ ^ 2 ≤ ‖circleMap 0 r θ - ρ‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hR]
    nlinarith [h_cos_law r, h_cos_law R, mul_le_mul_of_nonneg_left hr₀r hR.le,
      mul_le_mul_of_nonneg_left hrR hR.le, neg_one_le_cos, cos_le_one]
  grw [← sqrt_sq (norm_nonneg _), ← sqrt_mul (by positivity), this, sqrt_sq (norm_nonneg _)]

-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Computation for the
-- boundedness required by the dominated convergence theorem, Part II.
/-
**norm_herglotzLogIntegrand_circleMap_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma norm_herglotzLogIntegrand_circleMap_le {w ρ : ℂ} {R r₀ r : ℝ} (hR : 0 < R)
  (hρ : ‖ρ‖ = R) (hr₀ : 0 < r₀) (hw : ‖w‖ < r₀) (hr₀r : r₀ ≤ r) (hrR : r ≤ R) (θ : ℝ)
  (hdR : 0 < ‖circleMap 0 R θ - ρ‖) :
  ‖herglotzLogIntegrand w ρ (circleMap 0 r θ)‖ ≤ ((R + ‖w‖) / (r₀ - ‖w‖))
    * (|log (2 * R)| + |log (sqrt (r₀ / R))| + |log ‖circleMap 0 R θ - ρ‖|) := by
  simp only [herglotzLogIntegrand, Pi.smul_apply', Function.comp_apply, smul_eq_mul, norm_mul,
    norm_eq_abs]
  have ⟨hrw, hr⟩ : 0 < r₀ - ‖w‖ ∧ 0 < r := by grind
  have h_norm_sub₁ := const_mul_norm_sub_circleMap_le_norm_sub_circleMap hρ hr₀ hR hr₀r hrR θ
  have h_norm_sub₂ : 0 < ‖circleMap 0 r θ - ρ‖ := lt_of_lt_of_le (by positivity) h_norm_sub₁
  gcongr
  · simp only [herglotzRieszKernel_def, sub_zero]
    calc
     |((circleMap 0 r θ + w) / (circleMap 0 r θ - w)).re|
     _ ≤ ‖circleMap 0 r θ + w‖ / ‖circleMap 0 r θ - w‖ := by grw [Complex.abs_re_le_norm, norm_div]
     _ ≤ (r + ‖w‖) / (r - ‖w‖) := by
        grw [norm_add_le, ← norm_sub_norm_le]
        all_goals simp only [norm_circleMap_zero, abs_of_pos hr]; grind
      _ ≤ (R + ‖w‖) / (r₀ - ‖w‖) := by gcongr
  · apply abs_le.mpr ⟨_, _⟩
    · have h_log_lower_bound :
          log ‖circleMap 0 r θ - ρ‖ ≥ log (sqrt (r₀ / R)) + log ‖circleMap 0 R θ - ρ‖ := by
        rw [← log_mul (by positivity) (by positivity)]
        gcongr
      grind
    · calc log ‖circleMap 0 r θ - ρ‖
      _ ≤ |log (2 * R)| + 0 + 0 := by
        grw [← le_abs_self, norm_sub_le, hρ, two_mul, norm_circleMap_zero, abs_of_pos hr, hrR]
        simp
      _ ≤ |log (2 * R)| + |log √(r₀ / R)| + |log ‖circleMap 0 R θ - ρ‖| := by
        gcongr <;> positivity

-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Dominated convergence
-- theorem: circle average can be computed by a sequence of circle averages integrating over circles
-- in the interior
/-
**herglotzLogIntegrand_circleAverage_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem herglotzLogIntegrand_circleAverage_tendsto {ρ w : ℂ} {R : ℝ} (hR : 0 < R)
    (hρ : ‖ρ‖ = R) (hw : ‖w‖ < R) {r : ℕ → ℝ} (hr_lt : ∀ n, r n < R)
    (hr_tendsto : Tendsto r atTop (nhds R)) :
    Tendsto (fun n ↦ circleAverage (herglotzLogIntegrand w ρ) 0 (r n)) atTop
      (nhds (circleAverage (herglotzLogIntegrand w ρ) 0 R)) := by
  -- Apply the dominated convergence theorem.
  let bound := fun θ ↦ ((R + ‖w‖) / ((R + ‖w‖) / 2 - ‖w‖)) * (|log (2 * R)|
    + |log (sqrt ((R + ‖w‖) / 2 / R))| + |log ‖circleMap 0 R θ - ρ‖|)
  apply Filter.Tendsto.smul tendsto_const_nhds _
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
  · -- The herglotzLogIntegrand is AEStronglyMeasurable
    filter_upwards [hr_tendsto.eventually (lt_mem_nhds hw)] with n hn
    exact continuous_herglotzLogIntegrand_circle hρ (hr_lt n) hn |>.aestronglyMeasurable
  · -- Pointwise boundedness outside a null set
    filter_upwards [hr_tendsto.eventually (le_mem_nhds (by linarith : (R + ‖w‖) / 2 < R))] with n hn
    have h_bound {θ : ℝ} :
        ‖herglotzLogIntegrand w ρ (circleMap 0 (r n) θ)‖ ≤ bound θ ∨ ‖circleMap 0 R θ - ρ‖ = 0 := by
      refine Classical.or_iff_not_imp_right.mpr fun h ↦ ?_
      apply norm_herglotzLogIntegrand_circleMap_le hR hρ (by positivity) (by linarith) hn
        (hr_lt n).le
      simpa using! h
    apply measure_mono_null (t := {θ | ‖circleMap 0 R θ - ρ‖ = 0}) (by grind)
    simpa [sub_eq_zero] using!
      (countable_singleton ρ).preimage_circleMap 0 (hR.ne') |>.measure_zero _
  · -- IntervalIntegrable bound volume 0 (2 * π)
    apply (IntervalIntegrable.add (by simp) (by simp)).add ?_ |>.const_mul
    exact .abs <| MeromorphicOn.circleIntegrable_log_norm (f := fun z ↦ z - ρ) (by intro; fun_prop)
  · -- Pointwise convergence outside a null set
    have h_measure_zero : volume {θ : ℝ | circleMap 0 R θ = w ∨ circleMap 0 R θ = ρ} = 0 :=
      countable_singleton w |>.preimage_circleMap 0 (hR.ne') |>.union
        ((countable_singleton ρ).preimage_circleMap 0 (hR.ne')) |>.measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h_measure_zero] with θ hθ _
    apply (continuousAt_herglotzLogIntegrand (by tauto) (by tauto)).tendsto.comp
    exact tendsto_const_nhds.add <|
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hr_tendsto).mul tendsto_const_nhds

-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Statement in case where the
-- center equals zero.
/-
**circleAverage_re_herglotzRieszKernel_mul_log** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleAverage_re_herglotzRieszKernel_mul_log {w ρ c : Complex} {R : Real} 
(hρ : ρ in sphere c R) (hw : w in ball c R) : circleAverage ((Complex.re ∘ hergl
otzRieszKernel c w) * (log ‖· - ρ‖)) c R = log ‖w - ρ‖
参数：hρ : ρ in sphere c R；hw : w in ball c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用引理 `herglotzRieszKernel_add_const`：herglotzRieszKernel_add_const (c w z : Co
mplex) : herglotzRieszKernel c w (z + c) = herglotzRieszKernel 0 (w - c) z
（共 39 条，此处仅展示前 30 条）
-/
theorem circleAverage_re_herglotzRieszKernel_mul_log₀ {w ρ : ℂ} {R : ℝ} (hρ : ρ ∈ sphere 0 R)
    (hw : w ∈ ball 0 R) :
    circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • (log ‖· - ρ‖)) (0 : ℂ) R
      = log ‖w - ρ‖ := by
  have hR : 0 < R := pos_of_mem_ball hw
  rw [mem_sphere_iff_norm, sub_zero] at hρ
  rw [mem_ball_iff_norm, sub_zero] at hw
  let r : ℕ → ℝ := fun n ↦ R - (R - ‖w‖) / (n + 2)
  have hr_lt (n : ℕ) : r n < R := by
    simp_all only [sub_lt_self_iff, sub_pos, div_pos_iff_of_pos_left, r]
    positivity
  have hr_pos (n : ℕ) : 0 < r n := by
    simp_all only [sub_lt_self_iff, sub_pos, div_pos_iff_of_pos_left, r]
    apply (div_lt_iff₀ (by linarith)).2
    calc R - ‖w‖
      _ ≤ R * 1 := by aesop
      _ < R * (n + 2) := by gcongr; grind
  have hr_tendsto : Tendsto r atTop (nhds R) :=
    sub_zero R ▸ (tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <|
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have DCT := herglotzLogIntegrand_circleAverage_tendsto hR hρ hw hr_lt hr_tendsto
  have {n : ℕ} : circleAverage (herglotzLogIntegrand w ρ) 0 (r n) = log ‖w - ρ‖ := by
    unfold herglotzLogIntegrand
    apply InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul
    · refine ⟨fun z hz ↦ ?_, fun x hx ↦ ?_⟩
      · exact AnalyticAt.harmonicAt_log_norm (by fun_prop) (by grind [mem_ball, dist_zero_right])
      · suffices ‖x - ρ‖ ≠ 0 by fun_prop
        suffices x ≠ ρ by simpa [sub_eq_zero]
        have key := by simpa using closure_ball_subset_closedBall hx
        grind
    · simp only [mem_ball, dist_zero_right, lt_sub_iff_add_lt, r]
      field_simp
      calc ‖w‖ * (n + 2) + (R - ‖w‖) = ‖w‖ * (n + 1) + R := by ring
        _ < R * (n + 1) + R := by gcongr
        _ = R * (n + 2) := by ring
  aesop

/--
Analogue of the **Poisson Integral Formula** for the circle average function `log ‖· - ρ‖` along the
circle with radius `‖ρ‖`.

- See `InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul` in the file
  `Mathlib/Analysis/Complex/Harmonic/Poisson` for the classic Poisson Integral Formula, for harmonic
  functions without logarithmic poles.

- See `MeromorphicOn.extract_zeros_poles` in the file
  `Mathlib/Analysis/Meromorphic/FactorizedRational` for a construction that splits factors of the
  form `· - ρ` off arbitrary meromorphic functions.
-/
/-
**circleAverage_re_herglotzRieszKernel_mul_log** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：circleAverage_re_herglotzRieszKernel_mul_log {w ρ c : Complex} {R : Real} 
(hρ : ρ in sphere c R) (hw : w in ball c R) : circleAverage ((Complex.re ∘ hergl
otzRieszKernel c w) * (log ‖· - ρ‖)) c R = log ‖w - ρ‖
参数：hρ : ρ in sphere c R；hw : w in ball c R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用引理 `herglotzRieszKernel_add_const`：herglotzRieszKernel_add_const (c w z : Co
mplex) : herglotzRieszKernel c w (z + c) = herglotzRieszKernel 0 (w - c) z
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Analogue of the **Poisson Integral Formula** for the circle average function `lo
g ‖· - ρ‖` along the
circle with radius `‖ρ‖`.

- See `InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_s
mul` in the file
  `Mathlib/Analysis/Complex/Harmonic/Poisson` for the classic Poisson Integral F
ormula, for harmonic
  functions without logarithmic poles.

- See `MeromorphicOn.extract_zeros_poles` in the file
  `Mathlib/Analysis/Meromorphic/FactorizedRational` for a construction that spli
ts factors of the
  form `· - ρ` off arbitrary meromorphic functions.
-/
theorem circleAverage_re_herglotzRieszKernel_mul_log {w ρ c : ℂ} {R : ℝ} (hρ : ρ ∈ sphere c R)
    (hw : w ∈ ball c R) :
    circleAverage ((Complex.re ∘ herglotzRieszKernel c w) * (log ‖· - ρ‖)) c R = log ‖w - ρ‖ := by
  simp only [← circleAverage_map_add_const, Pi.mul_apply, Function.comp_apply, add_zero]
  conv =>
    left; arg 1
    intro z
    rw [(by ring : (z + 0 + c) - ρ = z - (ρ - c))]
    arg 1; arg 1
    rw [add_zero, herglotzRieszKernel_add_const c w z]
  have : (fun z ↦ (herglotzRieszKernel 0 (w - c) z).re * log ‖z - (ρ - c)‖) =
    (Complex.re ∘ herglotzRieszKernel 0 (w - c)) • (log ‖· - (ρ - c)‖) := by rfl
  rw [this, circleAverage_re_herglotzRieszKernel_mul_log₀ (by simp_all)
    (by simp_all [mem_ball_iff_norm.1 hw])]
  simp

/--
Let `D : ℂ → ℤ` be a function with locally finite support within the closed ball with center `c` and
radius `R`, such as the zero- and pole divisor of a meromorphic function.  Then, the circle average
of the function `∑ᶠ u, (D u * log ‖· - u‖)` over the boundary of the ball equals
`∑ᶠ u, D u * log R`.
-/
@[simp]
/-
**circleAverage_log_norm_factorizedRational** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：circleAverage_log_norm_factorizedRational {R : Real} {c : Complex} (D : Fu
nction.locallyFinsuppWithin (closedBall c |R|) Int) : circleAverage (∑ᶠ u, (D u 
* log ‖· - u‖)) c R = ∑ᶠ u, D u * log R
参数：D : Function.locallyFinsuppWithin (closedBall c |R|) Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.locallyFinsuppWithin.finiteSupport`：finiteSupport [T2Space X] [
Zero Y] (D : locallyFinsuppWithin U Y) (hU : IsCompact U) : Set.Finite D.support
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finsum_eq_sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_5} [inst :
 AddCommMonoid M] (f : α → M) {s : Finset α},   Function.support f ⊆ ↑s → ∑ᶠ (i 
: α), f i = ∑ i ∈ s, …
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Real.circleAverage_sum`：circleAverage_sum {ι : Type*} {s : Finset ι} {f 
: ι -> Complex -> E} (h : forall i in s, CircleIntegrable (f i) c R) : circleAve
rage (∑ i in…
· 使用定理 `IntervalIntegrable.const_mul`：const_mul {f : Real -> A} (hf : IntervalIn
tegrable f μ a b) (c : A) : IntervalIntegrable (fun x => c * f x) μ a b
· 使用定理 `MeromorphicOn.circleIntegrable_log_norm`：MeromorphicOn.circleIntegrable_
log_norm (hf : MeromorphicOn f (sphere c |R|)) : CircleIntegrable (log ‖f ·‖) c 
R
· 使用引理 `AnalyticOnNhd.meromorphicOn`：AnalyticOnNhd.meromorphicOn {f : 𝕜 -> E} {U
 : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) : MeromorphicOn f U
· 使用定理 `AnalyticOnNhd.sub`：AnalyticOnNhd.sub (hf : AnalyticOnNhd 𝕜 f s) (hg : An
alyticOnNhd 𝕜 g s) : AnalyticOnNhd 𝕜 (f - g) s
· 使用定理 `analyticOnNhd_id`：analyticOnNhd_id : AnalyticOnNhd 𝕜 (fun x : E => x) s
· 使用定理 `analyticOnNhd_const`：analyticOnNhd_const {v : F} {s : Set E} : AnalyticO
nNhd 𝕜 (fun _ => v) s
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Real.circleAverage_fun_smul`：circleAverage_fun_smul : circleAverage (fun
 z => a • f z) c R = a • circleAverage f c R
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `circleAverage_log_norm_sub_const_of_mem_closedBall`：circleAverage_log_no
rm_sub_const_of_mem_closedBall (hu : a in closedBall c |R|) : circleAverage (log
 ‖· - a‖) c R = log R
· 使用引理 `Function.locallyFinsuppWithin.supportWithinDomain`：supportWithinDomain [
Zero Y] (D : locallyFinsuppWithin U Y) : D.support subseteq U
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.support_mul`：∀ {ι : Type u_1} {M₀ : Type u_4} [inst : MulZeroCl
ass M₀] [NoZeroDivisors M₀] (f g : ι → M₀),   (Function.support fun x => f x * g
 x) = Func…
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Let `D : ℂ → ℤ` be a function with locally finite support within the closed ball
 with center `c` and
radius `R`, such as the zero- and pole divisor of a meromorphic function.  Then,
 the circle average
of the function `∑ᶠ u, (D u * log ‖· - u‖)` over the boundary of the ball equals
`∑ᶠ u, D u * log R`.
-/
lemma circleAverage_log_norm_factorizedRational {R : ℝ} {c : ℂ}
    (D : Function.locallyFinsuppWithin (closedBall c |R|) ℤ) :
    circleAverage (∑ᶠ u, (D u * log ‖· - u‖)) c R = ∑ᶠ u, D u * log R := by
  have h := D.finiteSupport (isCompact_closedBall c |R|)
  calc circleAverage (∑ᶠ u, (D u * log ‖· - u‖)) c R
  _ = circleAverage (∑ u ∈ h.toFinset, (D u * log ‖· - u‖)) c R := by
    rw [finsum_eq_sum_of_support_subset]
    intro u
    contrapose
    aesop
  _ = ∑ i ∈ h.toFinset, circleAverage (fun x ↦ D i * log ‖x - i‖) c R := by
    rw [circleAverage_sum]
    intro u hu
    apply IntervalIntegrable.const_mul
    apply (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm
  _ = ∑ u ∈ h.toFinset, D u * log R := by
    apply Finset.sum_congr rfl
    intro u hu
    simp_rw [← smul_eq_mul, circleAverage_fun_smul]
    congr
    rw [circleAverage_log_norm_sub_const_of_mem_closedBall]
    apply D.supportWithinDomain
    simp_all
  _ = ∑ᶠ u, D u * log R := by
    rw [finsum_eq_sum_of_support_subset]
    intro u
    aesop

/--
If  `g : ℂ → ℂ` is analytic without zero on the closed ball with center `c` and radius `R`, then the
circle average `circleAverage (log ‖g ·‖) c R` equals `log ‖g c‖`.
-/
@[simp]
/-
**AnalyticOnNhd.circleAverage_log_norm_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.circleAverage_log_norm_of_ne_zero {R : Real} {c : Complex} {
g : Complex -> Complex} (h₁g : AnalyticOnNhd Complex g (closedBall c |R|)) (h₂g 
: forall u in closedBall c |R|, g u != 0) : circleAverage (Real.log ‖g ·‖) c R =
 Real.log ‖g c‖
参数：h₁g : AnalyticOnNhd Complex g (closedBall c |R|)；h₂g : forall u in closedBall
 c |R|, g u != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpace.HarmonicOnNhd.circleAverage_eq`：∀ {F : Type u_1} [inst
 : NormedAddCommGroup F] [inst_1 : NormedSpace ℝ F] [CompleteSpace F] {f : ℂ → F
} {c : ℂ} {R : ℝ},   InnerProductSpace…
· 使用定理 `AnalyticAt.harmonicAt_log_norm`：AnalyticAt.harmonicAt_log_norm {f : Comp
lex -> Complex} {z : Complex} (h₁f : AnalyticAt Complex f z) (h₂f : f z != 0) : 
HarmonicAt (Real.log…

--- 原说明 ---
If  `g : ℂ → ℂ` is analytic without zero on the closed ball with center `c` and 
radius `R`, then the
circle average `circleAverage (log ‖g ·‖) c R` equals `log ‖g c‖`.
-/
lemma AnalyticOnNhd.circleAverage_log_norm_of_ne_zero {R : ℝ} {c : ℂ} {g : ℂ → ℂ}
    (h₁g : AnalyticOnNhd ℂ g (closedBall c |R|)) (h₂g : ∀ u ∈ closedBall c |R|, g u ≠ 0) :
    circleAverage (Real.log ‖g ·‖) c R = Real.log ‖g c‖ :=
  InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    (fun x hx ↦ (h₁g x hx).harmonicAt_log_norm (h₂g x hx))

set_option backward.isDefEq.respectTransparency.types false in
/--
Reformulation of a finsum that appears in Jensen's formula and in the definition of the counting
function of Value Distribution Theory, as discussed in
`Mathlib/Analysis/Complex/ValueDistribution/CountingFunction.lean`.
-/
/-
**countingFunction_finsum_eq_finsum_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：countingFunction_finsum_eq_finsum_add {c : Complex} {R : Real} {D : Comple
x -> Int} (hR : R != 0) (hD : D.HasFiniteSupport) : ∑ᶠ u, D u * (log R - log ‖c 
- u‖) = ∑ᶠ u, D u * log (R * ‖c - u‖⁻¹) + D c * log R
参数：hR : R != 0；hD : D.HasFiniteSupport。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.support_mul`：∀ {ι : Type u_1} {M₀ : Type u_4} [inst : MulZeroCl
ass M₀] [NoZeroDivisors M₀] (f g : ι → M₀),   (Function.support fun x => f x * g
 x) = Func…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `finsum_eq_sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_5} [inst :
 AddCommMonoid M] (f : α → M) {s : Finset α},   Function.support f ⊆ ↑s → ∑ᶠ (i 
: α), f i = ∑ i ∈ s, …
· 使用定理 `Finset.sum_eq_sum_sdiff_singleton_add`：∀ {ι : Type u_1} {M : Type u_3} [
inst : AddCommMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} {i : ι},   i ∈ s
 → ∀ (f : ι → M), ∑ x ∈ s, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
（共 70 条，此处仅展示前 30 条）

--- 原说明 ---
Reformulation of a finsum that appears in Jensen's formula and in the definition
 of the counting
function of Value Distribution Theory, as discussed in
`Mathlib/Analysis/Complex/ValueDistribution/CountingFunction.lean`.
-/
lemma countingFunction_finsum_eq_finsum_add {c : ℂ} {R : ℝ} {D : ℂ → ℤ} (hR : R ≠ 0)
    (hD : D.HasFiniteSupport) :
    ∑ᶠ u, D u * (log R - log ‖c - u‖) = ∑ᶠ u, D u * log (R * ‖c - u‖⁻¹) + D c * log R := by
  by_cases h : c ∈ D.support
  · have {g : ℂ → ℝ} : (fun u ↦ D u * g u).support ⊆ hD.toFinset :=
      fun x ↦ by simp +contextual
    simp only [finsum_eq_sum_of_support_subset _ this,
      Finset.sum_eq_sum_sdiff_singleton_add ((Set.Finite.mem_toFinset hD).mpr h), sub_self,
      norm_zero, log_zero, sub_zero, inv_zero, mul_zero, add_zero, add_left_inj]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp only [Finset.mem_sdiff, Finset.notMem_singleton] at hx
    rw [log_mul hR (inv_ne_zero (norm_ne_zero_iff.mpr (sub_eq_zero.not.2 hx.2.symm))), log_inv]
    ring
  · simp_all only [Function.mem_support, Decidable.not_not, Int.cast_zero, zero_mul, add_zero]
    refine finsum_congr fun x ↦ ?_
    by_cases h₁ : c = x
    · simp_all
    · rw [log_mul hR (inv_ne_zero (norm_ne_zero_iff.mpr (sub_eq_zero.not.2 h₁))), log_inv]
      ring

/-!
## Jensen's Formula
-/

/--
**Jensen's Formula**: If `f : ℂ → ℂ` is meromorphic on the closed ball with center `c` and radius
`R`, then the `circleAverage (log ‖f ·‖) c R` equals `log ‖meromorphicTrailingCoeffAt f c‖` plus a
correction term that accounts for the zeros and poles of `f` within the ball.

See `Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const` for a
reformulation in terms of the logarithmic counting function of Value Distribution Theory.
-/
/-
**MeromorphicOn.circleAverage_log_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeromorphicOn.circleAverage_log_norm {c : Complex} {R : Real} {f : Complex
 -> Complex} (hR : R != 0) (h₁f : MeromorphicOn f (closedBall c |R|)) : circleAv
erage (log ‖f ·‖) c R = ∑ᶠ u, divisor f (closedBall c |R|) u * log (R * ‖c - u‖⁻
¹) + divisor f (closedBall c |R|) c * log R + log ‖meromorphicTrailingCoeffAt f 
c‖
参数：hR : R != 0；h₁f : MeromorphicOn f (closedBall c |R|)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.locallyFinsuppWithin.finiteSupport`：finiteSupport [T2Space X] [
Zero Y] (D : locallyFinsuppWithin U Y) (hU : IsCompact U) : Set.Finite D.support
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `MeromorphicOn.extract_zeros_poles`：MeromorphicOn.extract_zeros_poles {f 
: 𝕜 -> E} (h₁f : MeromorphicOn f U) (h₂f : forall u : U, meromorphicOrderAt f u 
!= ⊤) (h₃f : (divisor f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MeromorphicOn.extract_zeros_poles_log`：MeromorphicOn.extract_zeros_poles
_log {f g : 𝕜 -> E} {D : Function.locallyFinsuppWithin U Int} (hg : forall u : U
, g u != 0) (h : f =ᶠ[codis…
· 使用定理 `Real.circleAverage_congr_codiscreteWithin`：circleAverage_congr_codiscret
eWithin (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hR : R != 0) : circleA
verage f₁ c R = circleAverage f…
· 使用引理 `Filter.codiscreteWithin_mono`：Filter.codiscreteWithin_mono {U₁ U : Set X
} (hU : U₁ subseteq U) : codiscreteWithin U₁ <= codiscreteWithin U
· 使用定理 `Metric.sphere_subset_closedBall`：sphere_subset_closedBall : sphere x ε s
ubseteq closedBall x ε
· 使用定理 `Real.circleAverage_add`：circleAverage_add (hf₁ : CircleIntegrable f₁ c R
) (hf₂ : CircleIntegrable f₂ c R) : circleAverage (f₁ + f₂) c R = circleAverage 
f₁ c R + cir…
· 使用定理 `circleIntegrable_log_norm_factorizedRational`：circleIntegrable_log_norm_
factorizedRational {R : Real} {c : Complex} (D : Complex -> Int) : CircleIntegra
ble (∑ᶠ u, ((D u) * log ‖· - u‖)) …
· 使用定理 `MeromorphicOn.circleIntegrable_log_norm`：MeromorphicOn.circleIntegrable_
log_norm (hf : MeromorphicOn f (sphere c |R|)) : CircleIntegrable (log ‖f ·‖) c 
R
· 使用引理 `AnalyticOnNhd.meromorphicOn`：AnalyticOnNhd.meromorphicOn {f : 𝕜 -> E} {U
 : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) : MeromorphicOn f U
· 使用定理 `AnalyticOnNhd.mono`：AnalyticOnNhd.mono {s t : Set E} (hf : AnalyticOnNhd
 𝕜 f t) (hst : s subseteq t) : AnalyticOnNhd 𝕜 f s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `circleAverage_log_norm_factorizedRational`：circleAverage_log_norm_factor
izedRational {R : Real} {c : Complex} (D : Function.locallyFinsuppWithin (closed
Ball c |R|) Int) : circleAverag…
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero`：AnalyticOnNhd.circleAve
rage_log_norm_of_ne_zero {R : Real} {c : Complex} {g : Complex -> Complex} (h₁g 
: AnalyticOnNhd Complex g (closedBall…
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 102 条，此处仅展示前 30 条）

--- 原说明 ---
**Jensen's Formula**: If `f : ℂ → ℂ` is meromorphic on the closed ball with cent
er `c` and radius
`R`, then the `circleAverage (log ‖f ·‖) c R` equals `log ‖meromorphicTrailingCo
effAt f c‖` plus a
correction term that accounts for the zeros and poles of `f` within the ball.

See `Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_cons
t` for a
reformulation in terms of the logarithmic counting function of Value Distributio
n Theory.
-/
theorem MeromorphicOn.circleAverage_log_norm {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0)
    (h₁f : MeromorphicOn f (closedBall c |R|)) :
    circleAverage (log ‖f ·‖) c R
      = ∑ᶠ u, divisor f (closedBall c |R|) u * log (R * ‖c - u‖⁻¹)
        + divisor f (closedBall c |R|) c * log R + log ‖meromorphicTrailingCoeffAt f c‖ := by
  -- Shorthand notation to keep line size in check
  let CB := closedBall c |R|
  by_cases h₂f : ∀ u ∈ CB, meromorphicOrderAt f u ≠ ⊤
  · have h₃f := (divisor f CB).finiteSupport (isCompact_closedBall c |R|)
    -- Extract zeros & poles and compute
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁f.extract_zeros_poles (by simp_all) h₃f
    calc circleAverage (log ‖f ·‖) c R
    _ = circleAverage ((∑ᶠ u, (divisor f CB u * log ‖· - u‖)) + (log ‖g ·‖)) c R := by
      have h₄g := extract_zeros_poles_log h₂g h₃g
      rw [circleAverage_congr_codiscreteWithin (codiscreteWithin_mono sphere_subset_closedBall h₄g)
        hR]
    _ = circleAverage (∑ᶠ u, (divisor f CB u * log ‖· - u‖)) c R + circleAverage (log ‖g ·‖) c R :=
      circleAverage_add (circleIntegrable_log_norm_factorizedRational (divisor f CB))
        ((h₁g.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm)
    _ = ∑ᶠ u, divisor f CB u * log R + log ‖g c‖ := by
      simp only [circleAverage_log_norm_factorizedRational, add_right_inj]
      rw [h₁g.circleAverage_log_norm_of_ne_zero]
      exact fun u hu ↦ h₂g ⟨u, hu⟩
    _ = ∑ᶠ u, divisor f CB u * log R
      + (log ‖meromorphicTrailingCoeffAt f c‖ - ∑ᶠ u, divisor f CB u * log ‖c - u‖) := by
      have t₀ : c ∈ CB := by simp [CB]
      have t₁ : AccPt c (𝓟 CB) := by
        apply accPt_iff_frequently_nhdsNE.mpr
        apply compl_notMem
        apply mem_nhdsWithin.mpr
        use ball c |R|
        simpa [hR] using! fun _ ⟨h, _⟩ ↦ ball_subset_closedBall h
      simp [MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles h₃f t₀ t₁
        (h₁f c t₀) (h₁g c t₀) (h₂g ⟨c, t₀⟩) h₃g]
    _ = ∑ᶠ u, divisor f CB u * log R - ∑ᶠ u, divisor f CB u * log ‖c - u‖
      + log ‖meromorphicTrailingCoeffAt f c‖ := by
      ring
    _ = (∑ᶠ u, divisor f CB u * (log R - log ‖c - u‖)) + log ‖meromorphicTrailingCoeffAt f c‖ := by
      rw [← finsum_sub_distrib]
      · simp_rw [← mul_sub]
      repeat apply h₃f.subset (fun _ ↦ (by simp_all))
    _ = ∑ᶠ u, divisor f CB u * log (R * ‖c - u‖⁻¹) + divisor f CB c * log R
      + log ‖meromorphicTrailingCoeffAt f c‖ := by
      rw [countingFunction_finsum_eq_finsum_add hR h₃f]
  · -- Trivial case: `f` vanishes on a codiscrete set
    have h₂f : ¬∀ (u : ↑(closedBall c |R|)), meromorphicOrderAt f ↑u ≠ ⊤ := by aesop
    rw [← h₁f.exists_meromorphicOrderAt_ne_top_iff_forall
      ⟨nonempty_closedBall.mpr (abs_nonneg R), (convex_closedBall c |R|).isPreconnected⟩] at h₂f
    push Not at h₂f
    have : divisor f CB = 0 := by
      ext x
      by_cases h : x ∈ CB
      <;> simp_all [CB]
    simp only [CB, this, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, Int.cast_zero,
      zero_mul, finsum_zero, add_zero, zero_add]
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top (by aesop), norm_zero, log_zero]
    have : f =ᶠ[codiscreteWithin CB] 0 := by
      filter_upwards [h₁f.meromorphicNFAt_mem_codiscreteWithin, self_mem_codiscreteWithin CB]
        with z h₁z h₂z
      simpa [h₂f ⟨z, h₂z⟩] using (not_iff_not.2 h₁z.meromorphicOrderAt_eq_zero_iff)
    rw [circleAverage_congr_codiscreteWithin (f₂ := 0) _ hR]
    · simp only [circleAverage, mul_inv_rev, Pi.zero_apply, intervalIntegral.integral_zero,
        smul_eq_mul, mul_zero]
    apply Filter.codiscreteWithin_mono (U := CB) sphere_subset_closedBall
    filter_upwards [this] with z hz
    simp_all

/-- **Jensen's Formula** specialized to the case that `f` is analytic and `f c ≠ 0`. -/
/-
**AnalyticOnNhd.circleAverage_log_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.circleAverage_log_norm {c : Complex} {R : Real} {f : Complex
 -> Complex} (hR : R != 0) (h₁f : AnalyticOnNhd Complex f (closedBall c |R|)) (h
₂f : f c != 0) : circleAverage (Real.log ‖f ·‖) c R = ∑ᶠ u, divisor f (closedBal
l c |R|) u * Real.log (R * ‖c - u‖⁻¹) + Real.log ‖f c‖
参数：hR : R != 0；h₁f : AnalyticOnNhd Complex f (closedBall c |R|)；h₂f : f c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeromorphicOn.circleAverage_log_norm`：MeromorphicOn.circleAverage_log_no
rm {c : Complex} {R : Real} {f : Complex -> Complex} (hR : R != 0) (h₁f : Meromo
rphicOn f (closedBall c |R…
· 使用引理 `AnalyticOnNhd.meromorphicOn`：AnalyticOnNhd.meromorphicOn {f : 𝕜 -> E} {U
 : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) : MeromorphicOn f U
· 使用定理 `MeromorphicOn.AnalyticOnNhd.divisor_apply`：∀ {𝕜 : Type u_1} [inst : Nont
riviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜} {E : Type u_2} [inst_1 : NormedAddCom
mGroup E]   [inst_2 : NormedSpa…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AnalyticAt.analyticOrderAt_eq_zero`：∀ {𝕜 : Type u_1} {E : Type u_2} [ins
t : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {f : 𝕜 → E} …
· 使用引理 `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero`：AnalyticAt.meromorphic
TrailingCoeffAt_of_ne_zero (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x != 0) : meromorphic
TrailingCoeffAt f x = f x
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用引理 `WithTop.untop₀_zero`：untop₀_zero : untop₀ 0 = (0 : α)
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Jensen's Formula** specialized to the case that `f` is analytic and `f c ≠ 0`.
-/
theorem AnalyticOnNhd.circleAverage_log_norm {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0)
    (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|))
    (h₂f : f c ≠ 0) :
    circleAverage (Real.log ‖f ·‖) c R
      = ∑ᶠ u, divisor f (closedBall c |R|) u * Real.log (R * ‖c - u‖⁻¹) + Real.log ‖f c‖ := by
  rw [h₁f.meromorphicOn.circleAverage_log_norm hR, h₁f.divisor_apply (by simp),
    (h₁f c (by simp)).analyticOrderAt_eq_zero.mpr h₂f,
    (h₁f c (by simp)).meromorphicTrailingCoeffAt_of_ne_zero h₂f]
  simp

/--
**Jensen's Inequality**: Estimates the number of zeros of `f` in a ball of radius `r`
given that `f` is analytic and bounded by `M` on a larger ball of radius `R`.
-/
/-
**AnalyticOnNhd.sum_divisor_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.sum_divisor_le {c : Complex} {r R M : Real} {f : Complex -> 
Complex} (r_pos : 0 < |r|) (r_lt_R : |r| < |R|) (hM : 1 <= M) (h₁f : AnalyticOnN
hd Complex f (closedBall c |R|)) (h₂f : f c != 0) (f_bound : forall z in sphere 
c |R|, ‖f z‖ <= M) : ∑ᶠ u, divisor f (closedBall c |r|) u <= Real.log (M / ‖f c‖
) / Real.log (R / r)
参数：r_pos : 0 < |r|；r_lt_R : |r| < |R|；hM : 1 <= M；h₁f : AnalyticOnNhd Complex f 
(closedBall c |R|)；h₂f : f c != 0；f_bound : forall z in sphere c |R|, ‖f z‖ <= M
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `map_finsum`：∀ {α : Type u_1} {M : Type u_5} {N : Type u_6} [inst : AddCo
mmMonoid M] [inst_1 : AddCommMonoid N] {f : α → M}   {G : Type u_7} [inst_2 : Fu
…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Function.locallyFinsuppWithin.finiteSupport`：finiteSupport [T2Space X] [
Zero Y] (D : locallyFinsuppWithin U Y) (hU : IsCompact U) : Set.Finite D.support
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用定理 `one_lt_div`：one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `AnalyticOnNhd.circleAverage_log_norm`：AnalyticOnNhd.circleAverage_log_no
rm {c : Complex} {R : Real} {f : Complex -> Complex} (hR : R != 0) (h₁f : Analyt
icOnNhd Complex f (closedB…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_ne_zero`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder 
α] [AddLeftMono α] {a : α} [AddRightMono α], |a| ≠ 0 ↔ a ≠ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
（共 158 条，此处仅展示前 30 条）

--- 原说明 ---
**Jensen's Inequality**: Estimates the number of zeros of `f` in a ball of radiu
s `r`
given that `f` is analytic and bounded by `M` on a larger ball of radius `R`.
-/
theorem AnalyticOnNhd.sum_divisor_le {c : ℂ} {r R M : ℝ} {f : ℂ → ℂ} (r_pos : 0 < |r|)
    (r_lt_R : |r| < |R|) (hM : 1 ≤ M) (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|))
    (h₂f : f c ≠ 0)
    (f_bound : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M) :
    ∑ᶠ u, divisor f (closedBall c |r|) u ≤ Real.log (M / ‖f c‖) / Real.log (R / r) := by
  -- Push the coerssion inside the sum
  trans ∑ᶠ u, (divisor f (closedBall c |r|) u : ℝ)
  · exact map_finsum (Int.castRingHom ℝ)
      ((divisor _ _).finiteSupport <| isCompact_closedBall ..) |>.le
  -- Rearrange: move `log R/r` to the LHS and inside the sum.
  have hrR : 1 < |R / r| := by simpa [abs_div, one_lt_div r_pos]
  suffices ∑ᶠ u, divisor f (closedBall c |r|) u * Real.log (R / r) ≤ Real.log (M / ‖f c‖) by
    rwa [← finsum_mul, ← le_div_iff₀] at this
    simpa using log_pos hrR
  have jensen := h₁f.circleAverage_log_norm (abs_ne_zero.mp (by linarith)) h₂f
  -- Estimate the circleAverage using the bound on f
  have integral_bound : circleAverage (fun x ↦ Real.log ‖f x‖) c R ≤ Real.log M := by
    apply circleAverage_mono_on_of_le_circle
    · exact (h₁f.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    · peel f_bound with z hz _
      obtain (h | h) := eq_zero_or_norm_pos (f z)
      · simpa [h] using log_nonneg hM
      · gcongr
  calc
  -- Bound by the sum from Jensen's formula
  _ ≤ ∑ᶠ u, ((divisor f (closedBall c |R|)) u) * Real.log (R * ‖c - u‖⁻¹) := by
    refine finsum_le_finsum' ?_ ?_ fun u ↦ ?_
    · exact (divisor f (closedBall c |r|)).finiteSupport (isCompact_closedBall ..) |>.subset
        fun _ _ ↦ (by simp_all)
    · exact (divisor f (closedBall c |R|)).finiteSupport (isCompact_closedBall ..) |>.subset
        fun _ _ ↦ (by simp_all)
    · -- Core bound: estimate the summand by splitting on which ball u is in
      by_cases h1 : u ∈ closedBall c |R|
      · by_cases h2 : u ∈ closedBall c |r|
        · --In the smaller ball: the divisors agree and we bound the log factor
          simp only [(h₁f.mono (closedBall_subset_closedBall r_lt_R.le)), h2,
            AnalyticOnNhd.divisor_apply, h₁f, h1]
          by_cases! h3 : u = c --Need to use the divisor is 0 at c rather than comparing the logs
          · rw [h3, (h₁f c (by simp)).analyticOrderAt_eq_zero.mpr h₂f]
            simp
          simp +singlePass only [← log_abs]
          gcongr 2
          · simp
          · have : ‖c - u‖ ≠ 0 := by simpa [sub_eq_zero] using h3.symm
            simpa [field, abs_div, r_pos.trans r_lt_R, dist_eq_norm'] using h2
        · --In the larger ball but not the smaller so LHS is 0 and RHS nonnegative
          simp only [h2, not_false_eq_true, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
            Int.cast_zero, zero_mul]
          refine mul_nonneg (mod_cast h₁f.divisor_nonneg ..) ?_
          apply log_abs _ ▸ log_nonneg
          simp only [mem_closedBall, dist_eq_norm', not_le] at h1 h2
          have : ‖c - u‖ ≠ 0 := (r_pos.trans h2).ne'
          simpa [field]
      · --Outside the larger ball so both sides are 0
        have : u ∉ closedBall c |r| := by
          simp_all
          linarith
        simp [h1, this]
  _ ≤ Real.log M - Real.log ‖f c‖ := by linarith --Uses jensen and integral_bound
  _ = _ := by rw [← log_div (by linarith) (norm_ne_zero_iff.mpr h₂f)]
