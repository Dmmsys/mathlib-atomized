/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Dedekind eta function

## Main definitions

* We define the Dedekind eta function as the infinite product
  `η(z) = q ^ 1/24 * ∏' (1 - q ^ (n + 1))` where `q = e ^ (2πiz)` and `z` is in the upper
  half-plane. The product is taken over all non-negative integers `n`. We then show it is
  non-vanishing and differentiable on the upper half-plane. Lastly, we compute its logarithmic
  derivative and show that it is a multiple of the Eisenstein series `E2`.

## References
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], section 1.2
-/

@[expose] public section

open Set Function Complex
open UpperHalfPlane hiding I
open scoped Real

local notation "𝕢" => Periodic.qParam

local notation "ℍₒ" => upperHalfPlaneSet

namespace ModularForm

/--
Definition of `eta_q` / `eta_q` 的定义

English:
abbreviation eta_q
  signature: (n : Nat) (z : Complex)
  body: (𝕢 1 z) ^ (n + 1)

中文:
缩写 eta_q
  签名: (n : 自然数) (z : Complex)
  定义体: (𝕢 1 z) ^ (n + 1)
-/
noncomputable abbrev eta_q (n : Nat) (z : Complex) := (𝕢 1 z) ^ (n + 1)

/--
lemma `eta_q_eq_cexp` / 引理 `eta_q_eq_cexp`

English:
lemma eta_q_eq_cexp
  given: (n : Nat) (z : Complex)
  statement: eta_q n z = cexp (2 * π * I * (n + 1) * z)
  proof: by
  simp [eta_q, Periodic.qParam, ← Complex.exp_nsmul]
  ring_nf

中文:
引理 eta_q_eq_cexp
  条件: (n : 自然数) (z : Complex)
  结论: eta_q n z = cexp (2 * π * I * (n + 1) * z)
  证明: by
  simp [eta_q, Periodic.qParam, ← Complex.exp_nsmul]
  ring_nf

Depends on / 依赖: Complex.exp_nsmul, Periodic, Periodic.qParam, eta_q, exp_nsmul, qParam, ring_nf
-/
lemma eta_q_eq_cexp (n : Nat) (z : Complex) : eta_q n z = cexp (2 * π * I * (n + 1) * z) := by
  simp [eta_q, Periodic.qParam, ← Complex.exp_nsmul]
  ring_nf

/--
lemma `eta_q_eq_pow` / 引理 `eta_q_eq_pow`

English:
lemma eta_q_eq_pow
  given: (n : Nat) (z : Complex)
  statement: eta_q n z = cexp (2 * π * I * z) ^ (n + 1)
  proof: by
  simp [eta_q, Periodic.qParam]

中文:
引理 eta_q_eq_pow
  条件: (n : 自然数) (z : Complex)
  结论: eta_q n z = cexp (2 * π * I * z) ^ (n + 1)
  证明: by
  simp [eta_q, Periodic.qParam]

Depends on / 依赖: Periodic, Periodic.qParam, eta_q, qParam
-/
lemma eta_q_eq_pow (n : Nat) (z : Complex) : eta_q n z = cexp (2 * π * I * z) ^ (n + 1) := by
  simp [eta_q, Periodic.qParam]

/--
lemma `one_sub_eta_q_ne_zero` / 引理 `one_sub_eta_q_ne_zero`

English:
lemma one_sub_eta_q_ne_zero
  given: (n : Nat) {z : Complex} (hz : z in ℍₒ)
  statement: 1 - eta_q n z != 0
  proof: by
  rw [eta_q_eq_cexp]; rw [sub_ne_zero]
  intro h
  simpa [← mul_assoc, ← h] using norm_exp_two_pi_I_lt_one ⟨(n + 1) • z, by
    simpa [(show 0 < (n + 1 : Real) by positivity)] using hz⟩

中文:
引理 one_sub_eta_q_ne_zero
  条件: (n : 自然数) {z : Complex} (hz : z in ℍₒ)
  结论: 1 - eta_q n z != 0
  证明: by
  rw [eta_q_eq_cexp]; rw [sub_ne_zero]
  intro h
  simpa [← mul_assoc, ← h] using norm_exp_two_pi_I_lt_one ⟨(n + 1) • z, by
    simpa [(show 0 < (n + 1 : Real) by positivity)] using hz⟩

Depends on / 依赖: eta_q_eq_cexp, mul_assoc, norm_exp_two_pi_I_lt_one, sub_ne_zero
-/
lemma one_sub_eta_q_ne_zero (n : Nat) {z : Complex} (hz : z in ℍₒ) : 1 - eta_q n z != 0 := by
  rw [eta_q_eq_cexp]; rw [sub_ne_zero]
  intro h
  simpa [← mul_assoc, ← h] using norm_exp_two_pi_I_lt_one ⟨(n + 1) • z, by
    simpa [(show 0 < (n + 1 : Real) by positivity)] using hz⟩

/--
Definition of `eta` / `eta` 的定义

English:
definition eta
  signature: (z : Complex)
  body: 𝕢 24 z * ∏' n, (1 - eta_q n z)

中文:
定义 eta
  签名: (z : Complex)
  定义体: 𝕢 24 z * ∏' n, (1 - eta_q n z)

Depends on / 依赖: eta_q
-/
noncomputable def eta (z : Complex) := 𝕢 24 z * ∏' n, (1 - eta_q n z)

/-- Notation for the Dedekind eta function. -/
scoped[ModularForm] notation "η" => eta

/--
lemma `multipliable_one_sub_pow` / 引理 `multipliable_one_sub_pow`

English:
lemma multipliable_one_sub_pow
  given: {q : Complex} (hq : ‖q‖ < 1)
  proof: by
  apply multipliable_one_add_of_summable (f := fun n => -q ^ (n + 1))
  simpa using (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq)

中文:
引理 multipliable_one_sub_pow
  条件: {q : Complex} (hq : ‖q‖ < 1)
  证明: by
  apply multipliable_one_add_of_summable (f := fun n => -q ^ (n + 1))
  simpa using (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq)

Depends on / 依赖: multipliable_one_add_of_summable, norm_nonneg, summable_geometric_of_lt_one, summable_nat_add_iff
-/
lemma multipliable_one_sub_pow {q : Complex} (hq : ‖q‖ < 1) :
    Multipliable fun n : Nat => 1 - q ^ (n + 1) := by
  apply multipliable_one_add_of_summable (f := fun n => -q ^ (n + 1))
  simpa using (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq)

/--
lemma `multipliableLocallyUniformlyOn_one_sub_pow` / 引理 `multipliableLocallyUniformlyOn_one_sub_pow`

English:
lemma multipliableLocallyUniformlyOn_one_sub_pow
  proof: by
  use fun q => ∏' n, (1 - q ^ (n + 1))
  simp_rw [sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact Metric.isOpen_ball
  intro K hK hcK
  rcases K.eq_empty_or_nonempty with hN | hN
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn, hN] using tendstoUniformlyOn_empty
  · obtai

中文:
引理 multipliableLocallyUniformlyOn_one_sub_pow
  证明: by
  use fun q => ∏' n, (1 - q ^ (n + 1))
  simp_rw [sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact Metric.isOpen_ball
  intro K hK hcK
  rcases K.eq_empty_or_nonempty with hN | hN
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn, hN] using tendstoUniformlyOn_empty
  · obtai

Depends on / 依赖: ContinuousOn, K.eq_empty_or_nonempty, Metric, Metric.isOpen_ball, eq_empty_or_nonempty, exists_sSup_image_eq_and_ge, fun_prop, hasProdLocallyUniformlyOn_of_forall_compact, hasProdUniformlyOn_iff_tendstoUniformlyOn, hcK.exists_sSup_image_eq_and_ge, isOpen_ball, norm_nonneg, simp_rw, sub_eq_add_neg, summable_geometric_of_lt_one, summable_nat_add_iff, tendstoUniformlyOn_empty
-/
lemma multipliableLocallyUniformlyOn_one_sub_pow :
    MultipliableLocallyUniformlyOn (fun n q => 1 - q ^ (n + 1)) (Metric.ball (0 : Complex) 1) := by
  use fun q => ∏' n, (1 - q ^ (n + 1))
  simp_rw [sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact Metric.isOpen_ball
  intro K hK hcK
  rcases K.eq_empty_or_nonempty with hN | hN
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn, hN] using tendstoUniformlyOn_empty
  · obtain ⟨q₀, hq₀, _, HB⟩ := hcK.exists_sSup_image_eq_and_ge hN
      (show ContinuousOn (fun q : Complex => ‖q‖) K by fun_prop)
    refine ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _)
      (by simpa [Metric.mem_ball, dist_zero_right] using hK hq₀))).hasProdUniformlyOn_nat_one_add
      hcK (.of_forall fun n x hx => ?_) (fun _ => by fun_prop)
    simpa using pow_le_pow_left₀ (norm_nonneg _) (HB x hx) (n + 1)

/--
lemma `differentiableOn_tprod_one_sub_pow` / 引理 `differentiableOn_tprod_one_sub_pow`

English:
lemma differentiableOn_tprod_one_sub_pow
  proof: multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn.differentiableOn
    (.of_forall fun _ => by simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun _ _ => by fun_prop)) Metric.isOpen_ball

中文:
引理 differentiableOn_tprod_one_sub_pow
  证明: multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn.differentiableOn
    (.of_forall fun _ => by simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun _ _ => by fun_prop)) Metric.isOpen_ball

Depends on / 依赖: DifferentiableOn, DifferentiableOn.finsetProd, Finset, Finset.prod_fn, Metric, Metric.isOpen_ball, differentiableOn, finsetProd, fun_prop, hasProdLocallyUniformlyOn, isOpen_ball, multipliableLocallyUniformlyOn_one_sub_pow, multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn.differentiableOn, of_forall, prod_fn
-/
lemma differentiableOn_tprod_one_sub_pow :
    DifferentiableOn Complex (fun q => ∏' n, (1 - q ^ (n + 1))) (Metric.ball (0 : Complex) 1) :=
  multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn.differentiableOn
    (.of_forall fun _ => by simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun _ _ => by fun_prop)) Metric.isOpen_ball

/--
lemma `differentiableOn_tprod_one_sub_pow_pow` / 引理 `differentiableOn_tprod_one_sub_pow_pow`

English:
lemma differentiableOn_tprod_one_sub_pow_pow
  given: (k : Nat)
  proof: (differentiableOn_tprod_one_sub_pow.fun_pow k).congr fun _ hq =>
    (multipliable_one_sub_pow (by simpa using hq)).tprod_pow k

中文:
引理 differentiableOn_tprod_one_sub_pow_pow
  条件: (k : 自然数)
  证明: (differentiableOn_tprod_one_sub_pow.fun_pow k).congr fun _ hq =>
    (multipliable_one_sub_pow (by simpa using hq)).tprod_pow k

Depends on / 依赖: differentiableOn_tprod_one_sub_pow, differentiableOn_tprod_one_sub_pow.fun_pow, fun_pow, multipliable_one_sub_pow, tprod_pow
-/
lemma differentiableOn_tprod_one_sub_pow_pow (k : Nat) :
    DifferentiableOn Complex (fun q => ∏' n, (1 - q ^ (n + 1)) ^ k) (Metric.ball (0 : Complex) 1) :=
  (differentiableOn_tprod_one_sub_pow.fun_pow k).congr fun _ hq =>
    (multipliable_one_sub_pow (by simpa using hq)).tprod_pow k

/--
theorem `summable_eta_q` / 定理 `summable_eta_q`

English:
theorem summable_eta_q
  given: (z : ℍ)
  statement: Summable fun n => ‖-eta_q n z‖
  proof: by
  simpa [summable_nat_add_iff] using
    summable_geometric_of_lt_one (norm_nonneg _) (mod_cast norm_qParam_lt_one 1 z)

中文:
定理 summable_eta_q
  条件: (z : ℍ)
  结论: Summable fun n => ‖-eta_q n z‖
  证明: by
  simpa [summable_nat_add_iff] using
    summable_geometric_of_lt_one (norm_nonneg _) (mod_cast norm_qParam_lt_one 1 z)

Depends on / 依赖: mod_cast, norm_nonneg, norm_qParam_lt_one, summable_geometric_of_lt_one, summable_nat_add_iff
-/
theorem summable_eta_q (z : ℍ) : Summable fun n => ‖-eta_q n z‖ := by
  simpa [summable_nat_add_iff] using
    summable_geometric_of_lt_one (norm_nonneg _) (mod_cast norm_qParam_lt_one 1 z)

/--
lemma `multipliableLocallyUniformlyOn_eta` / 引理 `multipliableLocallyUniformlyOn_eta`

English:
lemma multipliableLocallyUniformlyOn_eta
  proof: multipliableLocallyUniformlyOn_one_sub_pow.comp (𝕢 1)
    (fun z hz => by simpa using norm_qParam_lt_one 1 ⟨z, hz⟩) (by fun_prop)

中文:
引理 multipliableLocallyUniformlyOn_eta
  证明: multipliableLocallyUniformlyOn_one_sub_pow.comp (𝕢 1)
    (fun z hz => by simpa using norm_qParam_lt_one 1 ⟨z, hz⟩) (by fun_prop)

Depends on / 依赖: fun_prop, multipliableLocallyUniformlyOn_one_sub_pow, multipliableLocallyUniformlyOn_one_sub_pow.comp, norm_qParam_lt_one
-/
lemma multipliableLocallyUniformlyOn_eta :
    MultipliableLocallyUniformlyOn (fun n a => 1 - eta_q n a) ℍₒ :=
  multipliableLocallyUniformlyOn_one_sub_pow.comp (𝕢 1)
    (fun z hz => by simpa using norm_qParam_lt_one 1 ⟨z, hz⟩) (by fun_prop)

/--
lemma `eta_tprod_ne_zero` / 引理 `eta_tprod_ne_zero`

English:
lemma eta_tprod_ne_zero
  given: {z : Complex} (hz : z in ℍₒ)
  statement: ∏' n, (1 - eta_q n z) != 0
  proof: by
  refine tprod_one_add_ne_zero_of_summable (f := fun n => -eta_q n z) ?_ ?_
  · exact fun i => by simpa using! one_sub_eta_q_ne_zero i hz
  · simpa [eta_q, ← summable_norm_iff] using! summable_eta_q ⟨z, hz⟩

中文:
引理 eta_tprod_ne_zero
  条件: {z : Complex} (hz : z in ℍₒ)
  结论: ∏' n, (1 - eta_q n z) != 0
  证明: by
  refine tprod_one_add_ne_zero_of_summable (f := fun n => -eta_q n z) ?_ ?_
  · exact fun i => by simpa using! one_sub_eta_q_ne_zero i hz
  · simpa [eta_q, ← summable_norm_iff] using! summable_eta_q ⟨z, hz⟩

Depends on / 依赖: eta_q, one_sub_eta_q_ne_zero, summable_eta_q, summable_norm_iff, tprod_one_add_ne_zero_of_summable
-/
lemma eta_tprod_ne_zero {z : Complex} (hz : z in ℍₒ) : ∏' n, (1 - eta_q n z) != 0 := by
  refine tprod_one_add_ne_zero_of_summable (f := fun n => -eta_q n z) ?_ ?_
  · exact fun i => by simpa using! one_sub_eta_q_ne_zero i hz
  · simpa [eta_q, ← summable_norm_iff] using! summable_eta_q ⟨z, hz⟩

/--
lemma `eta_ne_zero` / 引理 `eta_ne_zero`

English:
lemma eta_ne_zero
  given: {z : Complex} (hz : z in ℍₒ)
  statement: η z != 0
  proof: mul_ne_zero (Periodic.qParam_ne_zero z) (eta_tprod_ne_zero hz)

中文:
引理 eta_ne_zero
  条件: {z : Complex} (hz : z in ℍₒ)
  结论: η z != 0
  证明: mul_ne_zero (Periodic.qParam_ne_zero z) (eta_tprod_ne_zero hz)

Depends on / 依赖: Periodic, Periodic.qParam_ne_zero, eta_tprod_ne_zero, mul_ne_zero, qParam_ne_zero
-/
lemma eta_ne_zero {z : Complex} (hz : z in ℍₒ) : η z != 0 :=
  mul_ne_zero (Periodic.qParam_ne_zero z) (eta_tprod_ne_zero hz)

/--
lemma `logDeriv_one_sub_cexp` / 引理 `logDeriv_one_sub_cexp`

English:
lemma logDeriv_one_sub_cexp
  given: (r : Complex)
  statement: logDeriv (fun z => 1 - r * cexp z) =
  proof: by
  ext z
  simp [logDeriv]

中文:
引理 logDeriv_one_sub_cexp
  条件: (r : Complex)
  结论: logDeriv (fun z => 1 - r * cexp z) =
  证明: by
  ext z
  simp [logDeriv]

Depends on / 依赖: logDeriv
-/
lemma logDeriv_one_sub_cexp (r : Complex) : logDeriv (fun z => 1 - r * cexp z) =
    fun z => -r * cexp z / (1 - r * cexp z) := by
  ext z
  simp [logDeriv]

/--
lemma `logDeriv_one_sub_mul_cexp_comp` / 引理 `logDeriv_one_sub_mul_cexp_comp`

English:
lemma logDeriv_one_sub_mul_cexp_comp
  given: (r : Complex) {g : Complex -> Complex} (hg : Differentiable Complex g)
  proof: by
  ext y
  rw [logDeriv_comp (by fun_prop) (hg y)]; rw [logDeriv_one_sub_cexp]
  ring

中文:
引理 logDeriv_one_sub_mul_cexp_comp
  条件: (r : Complex) {g : Complex -> Complex} (hg : Differentiable Complex g)
  证明: by
  ext y
  rw [logDeriv_comp (by fun_prop) (hg y)]; rw [logDeriv_one_sub_cexp]
  ring

Depends on / 依赖: fun_prop, logDeriv_comp, logDeriv_one_sub_cexp
-/
lemma logDeriv_one_sub_mul_cexp_comp (r : Complex) {g : Complex -> Complex} (hg : Differentiable Complex g) :
    logDeriv ((fun z => 1 - r * cexp z) ∘ g) =
    fun z => -r * (deriv g z) * cexp (g z) / (1 - r * cexp (g z)) := by
  ext y
  rw [logDeriv_comp (by fun_prop) (hg y)]; rw [logDeriv_one_sub_cexp]
  ring

/--
theorem `one_sub_eta_logDeriv_eq` / 定理 `one_sub_eta_logDeriv_eq`

English:
theorem one_sub_eta_logDeriv_eq
  given: (z : Complex) (n : Nat)
  proof: by
  have h2 : (fun x => 1 - cexp (2 * ↑π * I * (n + 1) * x)) =
      ((fun z => 1 - 1 * cexp z) ∘ fun x => 2 * ↑π * I * (n + 1) * x) := by aesop
  simp_rw [eta_q_eq_cexp, h2, logDeriv_one_sub_mul_cexp_comp 1
    (g := fun x => (2 * π * I * (n + 1) * x)) (by fun_prop), deriv_const_mul_id]
  simp

中文:
定理 one_sub_eta_logDeriv_eq
  条件: (z : Complex) (n : 自然数)
  证明: by
  have h2 : (fun x => 1 - cexp (2 * ↑π * I * (n + 1) * x)) =
      ((fun z => 1 - 1 * cexp z) ∘ fun x => 2 * ↑π * I * (n + 1) * x) := by aesop
  simp_rw [eta_q_eq_cexp, h2, logDeriv_one_sub_mul_cexp_comp 1
    (g := fun x => (2 * π * I * (n + 1) * x)) (by fun_prop), deriv_const_mul_id]
  simp
-/
private theorem one_sub_eta_logDeriv_eq (z : Complex) (n : Nat) :
    logDeriv (1 - eta_q n ·) z = 2 * π * I * (n + 1) * -eta_q n z / (1 - eta_q n z) := by
  have h2 : (fun x => 1 - cexp (2 * ↑π * I * (n + 1) * x)) =
      ((fun z => 1 - 1 * cexp z) ∘ fun x => 2 * ↑π * I * (n + 1) * x) := by aesop
  simp_rw [eta_q_eq_cexp, h2, logDeriv_one_sub_mul_cexp_comp 1
    (g := fun x => (2 * π * I * (n + 1) * x)) (by fun_prop), deriv_const_mul_id]
  simp

/--
lemma `tsum_logDeriv_eta_q` / 引理 `tsum_logDeriv_eta_q`

English:
lemma tsum_logDeriv_eta_q
  given: (z : Complex)
  statement: ∑' n, logDeriv (fun x => 1 - eta_q n x) z =
  proof: by
  rw [tsum_congr (one_sub_eta_logDeriv_eq z)]; rw [← tsum_mul_left]
  grind

中文:
引理 tsum_logDeriv_eta_q
  条件: (z : Complex)
  结论: ∑' n, logDeriv (fun x => 1 - eta_q n x) z =
  证明: by
  rw [tsum_congr (one_sub_eta_logDeriv_eq z)]; rw [← tsum_mul_left]
  grind

Depends on / 依赖: one_sub_eta_logDeriv_eq, tsum_congr, tsum_mul_left
-/
lemma tsum_logDeriv_eta_q (z : Complex) : ∑' n, logDeriv (fun x => 1 - eta_q n x) z =
    (2 * π * I) * ∑' n, (n + 1) * (-eta_q n z) / (1 - eta_q n z) := by
  rw [tsum_congr (one_sub_eta_logDeriv_eq z)]; rw [← tsum_mul_left]
  grind

/--
lemma `differentiableAt_eta_tprod` / 引理 `differentiableAt_eta_tprod`

English:
lemma differentiableAt_eta_tprod
  given: {z : Complex} (hz : z in ℍₒ)
  proof: by
  have hq : 𝕢 1 z in Metric.ball 0 1 := by simpa using norm_qParam_lt_one 1 ⟨z, hz⟩
  exact (differentiableOn_tprod_one_sub_pow.differentiableAt
    (Metric.isOpen_ball.mem_nhds hq)).comp z (by fun_prop)

中文:
引理 differentiableAt_eta_tprod
  条件: {z : Complex} (hz : z in ℍₒ)
  证明: by
  have hq : 𝕢 1 z in Metric.ball 0 1 := by simpa using norm_qParam_lt_one 1 ⟨z, hz⟩
  exact (differentiableOn_tprod_one_sub_pow.differentiableAt
    (Metric.isOpen_ball.mem_nhds hq)).comp z (by fun_prop)

Depends on / 依赖: Metric, Metric.ball, Metric.isOpen_ball.mem_nhds, differentiableAt, differentiableOn_tprod_one_sub_pow, differentiableOn_tprod_one_sub_pow.differentiableAt, fun_prop, isOpen_ball, mem_nhds, norm_qParam_lt_one
-/
lemma differentiableAt_eta_tprod {z : Complex} (hz : z in ℍₒ) :
    DifferentiableAt Complex (fun x => ∏' n, (1 - eta_q n x)) z := by
  have hq : 𝕢 1 z in Metric.ball 0 1 := by simpa using norm_qParam_lt_one 1 ⟨z, hz⟩
  exact (differentiableOn_tprod_one_sub_pow.differentiableAt
    (Metric.isOpen_ball.mem_nhds hq)).comp z (by fun_prop)

/--
theorem `differentiableAt_eta_of_mem_upperHalfPlaneSet` / 定理 `differentiableAt_eta_of_mem_upperHalfPlaneSet`

English:
theorem differentiableAt_eta_of_mem_upperHalfPlaneSet
  given: {z : Complex} (hz : z in ℍₒ)
  proof: .mul (by fun_prop) (differentiableAt_eta_tprod hz)

中文:
定理 differentiableAt_eta_of_mem_upperHalfPlaneSet
  条件: {z : Complex} (hz : z in ℍₒ)
  证明: .mul (by fun_prop) (differentiableAt_eta_tprod hz)

Depends on / 依赖: differentiableAt_eta_tprod, fun_prop
-/
theorem differentiableAt_eta_of_mem_upperHalfPlaneSet {z : Complex} (hz : z in ℍₒ) :
    DifferentiableAt Complex eta z :=
  .mul (by fun_prop) (differentiableAt_eta_tprod hz)

/--
lemma `logDeriv_qParam` / 引理 `logDeriv_qParam`

English:
lemma logDeriv_qParam
  given: (h : Real) (z : Complex)
  statement: logDeriv (𝕢 h) z = 2 * π * I / h
  proof: by
  have : 𝕢 h = cexp ∘ ((2 * π * I / h) * ·) := by
    ext
    grind [Periodic.qParam]
  rw [this]; rw [logDeriv_comp (by fun_prop) (by fun_prop)]; rw [deriv_const_mul_id]
  simp [logDeriv_exp]

中文:
引理 logDeriv_qParam
  条件: (h : 实数) (z : Complex)
  结论: logDeriv (𝕢 h) z = 2 * π * I / h
  证明: by
  have : 𝕢 h = cexp ∘ ((2 * π * I / h) * ·) := by
    ext
    grind [Periodic.qParam]
  rw [this]; rw [logDeriv_comp (by fun_prop) (by fun_prop)]; rw [deriv_const_mul_id]
  simp [logDeriv_exp]

Depends on / 依赖: Periodic, Periodic.qParam, deriv_const_mul_id, fun_prop, logDeriv_comp, logDeriv_exp, qParam
-/
lemma logDeriv_qParam (h : Real) (z : Complex) : logDeriv (𝕢 h) z = 2 * π * I / h := by
  have : 𝕢 h = cexp ∘ ((2 * π * I / h) * ·) := by
    ext
    grind [Periodic.qParam]
  rw [this]; rw [logDeriv_comp (by fun_prop) (by fun_prop)]; rw [deriv_const_mul_id]
  simp [logDeriv_exp]

/--
lemma `summable_logDeriv_one_sub_eta_q` / 引理 `summable_logDeriv_one_sub_eta_q`

English:
lemma summable_logDeriv_one_sub_eta_q
  given: {z : Complex} (hz : z in ℍₒ)
  proof: by
  have := summable_norm_pow_mul_geometric_div_one_sub 1 (norm_qParam_lt_one 1 ⟨z, hz⟩)
  convert! ((summable_nat_add_iff 1).mpr this).mul_left (-2 * π * I) using 1 with n
  grind [one_sub_eta_logDeriv_eq]

中文:
引理 summable_logDeriv_one_sub_eta_q
  条件: {z : Complex} (hz : z in ℍₒ)
  证明: by
  have := summable_norm_pow_mul_geometric_div_one_sub 1 (norm_qParam_lt_one 1 ⟨z, hz⟩)
  convert! ((summable_nat_add_iff 1).mpr this).mul_left (-2 * π * I) using 1 with n
  grind [one_sub_eta_logDeriv_eq]

Depends on / 依赖: convert, mul_left, norm_qParam_lt_one, one_sub_eta_logDeriv_eq, summable_nat_add_iff, summable_norm_pow_mul_geometric_div_one_sub
-/
lemma summable_logDeriv_one_sub_eta_q {z : Complex} (hz : z in ℍₒ) :
    Summable fun i => logDeriv (1 - eta_q i ·) z := by
  have := summable_norm_pow_mul_geometric_div_one_sub 1 (norm_qParam_lt_one 1 ⟨z, hz⟩)
  convert! ((summable_nat_add_iff 1).mpr this).mul_left (-2 * π * I) using 1 with n
  grind [one_sub_eta_logDeriv_eq]

open EisensteinSeries in
/--
lemma `logDeriv_eta_eq_E2` / 引理 `logDeriv_eta_eq_E2`

English:
lemma logDeriv_eta_eq_E2
  given: (z : ℍ)
  statement: logDeriv eta z = (π * I / 12) * E2 z
  proof: by
  unfold eta
  rw [logDeriv_mul _ (Periodic.qParam_ne_zero _) (eta_tprod_ne_zero z.2) (by fun_prop)
    (differentiableAt_eta_tprod z.2)]
  have HG := logDeriv_tprod_eq_tsum isOpen_upperHalfPlaneSet z.2
    (one_sub_eta_q_ne_zero · z.2) (by fun_prop) (summable_logDeriv_one_sub_eta_q z.2)
    mult

中文:
引理 logDeriv_eta_eq_E2
  条件: (z : ℍ)
  结论: logDeriv eta z = (π * I / 12) * E2 z
  证明: by
  unfold eta
  rw [logDeriv_mul _ (Periodic.qParam_ne_zero _) (eta_tprod_ne_zero z.2) (by fun_prop)
    (differentiableAt_eta_tprod z.2)]
  have HG := logDeriv_tprod_eq_tsum isOpen_upperHalfPlaneSet z.2
    (one_sub_eta_q_ne_zero · z.2) (by fun_prop) (summable_logDeriv_one_sub_eta_q z.2)
    mult

Depends on / 依赖: G2_eq_tsum_cexp, Periodic, Periodic.qParam_ne_zero, Pi.smul_apply, differentiableAt_eta_tprod, eta_tprod_ne_zero, fun_prop, isOpen_upperHalfPlaneSet, logDeriv_mul, logDeriv_qParam, logDeriv_tprod_eq_tsum, mul_inv_rev, multipliableLocallyUniformlyOn_eta, one_div, one_sub_eta_q_ne_zero, qParam_ne_zero, riemannZeta_two, smul_apply, smul_eq_mul, summable_logDeriv_one_sub_eta_q
-/
lemma logDeriv_eta_eq_E2 (z : ℍ) : logDeriv eta z = (π * I / 12) * E2 z := by
  unfold eta
  rw [logDeriv_mul _ (Periodic.qParam_ne_zero _) (eta_tprod_ne_zero z.2) (by fun_prop)
    (differentiableAt_eta_tprod z.2)]
  have HG := logDeriv_tprod_eq_tsum isOpen_upperHalfPlaneSet z.2
    (one_sub_eta_q_ne_zero · z.2) (by fun_prop) (summable_logDeriv_one_sub_eta_q z.2)
    multipliableLocallyUniformlyOn_eta (eta_tprod_ne_zero z.2)
  simp only [logDeriv_qParam 24 z, HG, tsum_logDeriv_eta_q z, E2, one_div,
    mul_inv_rev, Pi.smul_apply, smul_eq_mul]
  rw [G2_eq_tsum_cexp]; rw [riemannZeta_two]; rw [← tsum_pow_div_one_sub_eq_tsum_sigma
    (norm_exp_two_pi_I_lt_one z)]; rw [mul_sub]; rw [sub_eq_add_neg]; rw [mul_add]
  simp [eta_q_eq_pow, ← tsum_mul_left, tsum_pnat_eq_tsum_succ (f := fun n =>
        n * cexp (2 * π * I * z) ^ n / (1 - cexp (2 * π * I * z) ^ n)), ← tsum_neg]
  grind

end ModularForm
