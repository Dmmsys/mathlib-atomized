/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic

/-!
# Asymptotic Behavior of the Logarithmic Counting Function

If `f` is meromorphic over a field `𝕜`, we show that the logarithmic counting function for the
poles of `f` is asymptotically bounded if and only if `f` has only removable singularities. See
Page 170f of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.

Analogously, characterize meromorphic functions with finite set of poles, as functions whose
logarithmic counting function is big-O of `log`.

## Implementation Notes

We establish the result first for the logarithmic counting function for functions with locally
finite support on `𝕜` and then specialize to the setting where the function with locally finite
support is the pole or zero-divisor of a meromorphic function.
-/

public section

open Asymptotics Filter Function Real Set

namespace Function.locallyFinsuppWithin

variable
  {E : Type*} [NormedAddCommGroup E]

/-!
## Logarithmic Counting Functions for Functions with Locally Finite Support
-/

/--
lemma `one_isLittleO_logCounting_single` / 引理 `one_isLittleO_logCounting_single`

English:
lemma one_isLittleO_logCounting_single
  given: [DecidableEq E] [ProperSpace E] {e : E}
  proof: by
  have hΘ : (fun r => log r - log ‖e‖) =Θ[atTop] log :=
    (IsEquivalent.sub_isLittleO IsEquivalent.refl isLittleO_const_log_atTop).isTheta
  have h₁ : (1 : Real -> Real) =o[atTop] fun r => log r - log ‖e‖ :=
    (hΘ.isLittleO_congr_right).2 isLittleO_const_log_atTop
  refine h₁.congr' Eventuall

中文:
引理 one_isLittleO_logCounting_single
  条件: [DecidableEq E] [命题erSpace E] {e : E}
  证明: by
  have hΘ : (fun r => log r - log ‖e‖) =Θ[atTop] log :=
    (IsEquivalent.sub_isLittleO IsEquivalent.refl isLittleO_const_log_atTop).isTheta
  have h₁ : (1 : Real -> Real) =o[atTop] fun r => log r - log ‖e‖ :=
    (hΘ.isLittleO_congr_right).2 isLittleO_const_log_atTop
  refine h₁.congr' Eventuall

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl, IsEquivalent, IsEquivalent.refl, IsEquivalent.sub_isLittleO, eventually_ge_atTop, filter_upwards, isLittleO_congr_right, isLittleO_const_log_atTop, isTheta, logCounting_single_eq_log_sub_const, sub_isLittleO
-/
lemma one_isLittleO_logCounting_single [DecidableEq E] [ProperSpace E] {e : E} :
    (1 : Real -> Real) =o[atTop] logCounting (single e 1) := by
  have hΘ : (fun r => log r - log ‖e‖) =Θ[atTop] log :=
    (IsEquivalent.sub_isLittleO IsEquivalent.refl isLittleO_const_log_atTop).isTheta
  have h₁ : (1 : Real -> Real) =o[atTop] fun r => log r - log ‖e‖ :=
    (hΘ.isLittleO_congr_right).2 isLittleO_const_log_atTop
  refine h₁.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_ge_atTop ‖e‖] with r hr
  simp [logCounting_single_eq_log_sub_const hr]

/--
lemma `zero_iff_logCounting_bounded` / 引理 `zero_iff_logCounting_bounded`

English:
lemma zero_iff_logCounting_bounded
  statement: [ProperSpace E]
  proof: by
  classical
  refine ⟨fun h₂ => by simp [isBigO_of_le' (c := 0), h₂], ?_⟩
  contrapose
  intro h₁
  obtain ⟨e, he⟩ := exists_single_le_pos (lt_of_le_of_ne h (h₁ ·.symm))
  rw [isBigO_iff'']
  push Not
  intro a ha
  simp only [Pi.one_apply, norm_eq_abs, frequently_atTop, abs_one]
  intro b
  obta

中文:
引理 zero_iff_logCounting_bounded
  结论: [命题erSpace E]
  证明: by
  classical
  refine ⟨fun h₂ => by simp [isBigO_of_le' (c := 0), h₂], ?_⟩
  contrapose
  intro h₁
  obtain ⟨e, he⟩ := exists_single_le_pos (lt_of_le_of_ne h (h₁ ·.symm))
  rw [isBigO_iff'']
  push Not
  intro a ha
  simp only [Pi.one_apply, norm_eq_abs, frequently_atTop, abs_one]
  intro b
  obta

Depends on / 依赖: Pi.one_apply, abs_one, classical, contrapose, eventually_atTop, exists_single_le_pos, frequently_atTop, isBigO_iff, isBigO_of_le, isLittleO_iff, lt_of_le_of_ne, norm_eq_abs, one_apply, one_isLittleO_logCounting_single
-/
lemma zero_iff_logCounting_bounded [ProperSpace E]
    {D : locallyFinsuppWithin (univ : Set E) Int} (h : 0 <= D) :
    D = 0 ↔ logCounting D =O[atTop] (1 : Real -> Real) := by
  classical
  refine ⟨fun h₂ => by simp [isBigO_of_le' (c := 0), h₂], ?_⟩
  contrapose
  intro h₁
  obtain ⟨e, he⟩ := exists_single_le_pos (lt_of_le_of_ne h (h₁ ·.symm))
  rw [isBigO_iff'']
  push Not
  intro a ha
  simp only [Pi.one_apply, norm_eq_abs, frequently_atTop, abs_one]
  intro b
  obtain ⟨c, hc⟩ := eventually_atTop.1
    (isLittleO_iff.1 (one_isLittleO_logCounting_single (e := e)) ha)
  let ℓ := 1 + max ‖e‖ (max |b| |c|)
  have h₁ℓ : c <= ℓ := by grind
  have h₂ℓ : 1 <= ℓ := by simp [ℓ]
  use 1 + ℓ, (show b <= 1 + ℓ by grind)
  calc 1
    _ <= (a * |logCounting (single e 1) ℓ|) := by simpa [h₁ℓ] using hc ℓ
    _ <= (a * |logCounting D ℓ|) := by
      gcongr
      · apply logCounting_nonneg (single_pos.2 Int.one_pos).le h₂ℓ
      · apply logCounting_le he h₂ℓ
    _ < a * |logCounting D (1 + ℓ)| := by
      gcongr 2
      rw [abs_of_nonneg (logCounting_nonneg h h₂ℓ)]; rw [abs_of_nonneg (logCounting_nonneg h (by grind))]
      apply logCounting_strictMono he <;> grind

/--
lemma `logCounting_single_isBigO_log` / 引理 `logCounting_single_isBigO_log`

English:
lemma logCounting_single_isBigO_log
  given: [DecidableEq E] [ProperSpace E] {e : E} {n : Int}
  proof: by
  have h₁ : logCounting (single e n) =ᶠ[atTop] (n * log · - n * log ‖e‖) := by
    filter_upwards [eventually_ge_atTop ‖e‖] with r hr
    rw [logCounting_single_eq_log_sub_const hr]
    ring
  have hb : (n * log ·) =O[atTop] Real.log := isBigO_const_mul_self (n : Real) log atTop
  exact (hb.sub i

中文:
引理 logCounting_single_isBigO_log
  条件: [DecidableEq E] [命题erSpace E] {e : E} {n : 整数}
  证明: by
  have h₁ : logCounting (single e n) =ᶠ[atTop] (n * log · - n * log ‖e‖) := by
    filter_upwards [eventually_ge_atTop ‖e‖] with r hr
    rw [logCounting_single_eq_log_sub_const hr]
    ring
  have hb : (n * log ·) =O[atTop] Real.log := isBigO_const_mul_self (n : Real) log atTop
  exact (hb.sub i

Depends on / 依赖: EventuallyEq, EventuallyEq.rfl, Real.log, eventually_ge_atTop, filter_upwards, hb.sub, isBigO, isBigO_const_mul_self, isLittleO_const_log_atTop, isLittleO_const_log_atTop.isBigO, logCounting, logCounting_single_eq_log_sub_const, single
-/
lemma logCounting_single_isBigO_log [DecidableEq E] [ProperSpace E] {e : E} {n : Int} :
    logCounting (single e n) =O[atTop] Real.log := by
  have h₁ : logCounting (single e n) =ᶠ[atTop] (n * log · - n * log ‖e‖) := by
    filter_upwards [eventually_ge_atTop ‖e‖] with r hr
    rw [logCounting_single_eq_log_sub_const hr]
    ring
  have hb : (n * log ·) =O[atTop] Real.log := isBigO_const_mul_self (n : Real) log atTop
  exact (hb.sub isLittleO_const_log_atTop.isBigO).congr' h₁.symm EventuallyEq.rfl

/--
lemma `logCounting_isBigO_log_of_finite_support` / 引理 `logCounting_isBigO_log_of_finite_support`

English:
lemma logCounting_isBigO_log_of_finite_support
  statement: [ProperSpace E] {D : locallyFinsupp E Int}
  proof: by
  classical
  rw [← sum_apply_smul_single_eq_self_on_univ h]; rw [map_sum]
  exact Asymptotics.IsBigO.sum fun _ _ => logCounting_single_isBigO_log

中文:
引理 logCounting_isBigO_log_of_finite_support
  结论: [命题erSpace E] {D : locallyFinsupp E 整数}
  证明: by
  classical
  rw [← sum_apply_smul_single_eq_self_on_univ h]; rw [map_sum]
  exact Asymptotics.IsBigO.sum fun _ _ => logCounting_single_isBigO_log

Depends on / 依赖: Asymptotics, Asymptotics.IsBigO.sum, IsBigO, classical, logCounting_single_isBigO_log, map_sum, sum_apply_smul_single_eq_self_on_univ
-/
lemma logCounting_isBigO_log_of_finite_support [ProperSpace E] {D : locallyFinsupp E Int}
    (h : D.support.Finite) :
    logCounting D =O[atTop] Real.log := by
  classical
  rw [← sum_apply_smul_single_eq_self_on_univ h]; rw [map_sum]
  exact Asymptotics.IsBigO.sum fun _ _ => logCounting_single_isBigO_log

/--
lemma `finite_support_of_logCounting_isBigO_log` / 引理 `finite_support_of_logCounting_isBigO_log`

English:
lemma finite_support_of_logCounting_isBigO_log
  statement: [ProperSpace E]
  proof: by
  classical
  -- Let (N : ℕ) be a number such that ‖logCounting D x‖ ≤ N * ‖log x‖
  obtain ⟨C, hC⟩ := isBigO_iff.1 hO
  obtain ⟨N, hCN⟩ := exists_nat_gt (max C 0)
  have hCN' : C < N := lt_of_le_of_lt (le_max_left C 0) hCN
  -- Argue by contradiction, let t be a cardinality=N finite subset in th

中文:
引理 finite_support_of_logCounting_isBigO_log
  结论: [命题erSpace E]
  证明: by
  classical
  -- Let (N : ℕ) be a number such that ‖logCounting D x‖ ≤ N * ‖log x‖
  obtain ⟨C, hC⟩ := isBigO_iff.1 hO
  obtain ⟨N, hCN⟩ := exists_nat_gt (max C 0)
  have hCN' : C < N := lt_of_le_of_lt (le_max_left C 0) hCN
  -- Argue by contradiction, let t be a cardinality=N finite subset in th

Depends on / 依赖: classical
-/
lemma finite_support_of_logCounting_isBigO_log [ProperSpace E]
    {D : locallyFinsupp E Int} (h : 0 <= D) (hO : logCounting D =O[atTop] Real.log) :
    D.support.Finite := by
  classical
  -- Let (N : ℕ) be a number such that ‖logCounting D x‖ ≤ N * ‖log x‖
  obtain ⟨C, hC⟩ := isBigO_iff.1 hO
  obtain ⟨N, hCN⟩ := exists_nat_gt (max C 0)
  have hCN' : C < N := lt_of_le_of_lt (le_max_left C 0) hCN
  -- Argue by contradiction, let t be a cardinality=N finite subset in the (infinite) support of D
  -- and let D' be the divisor for the indicator function of t
  by_contra! hInf
  obtain ⟨t, htsub, htcard⟩ := hInf.exists_subset_card_eq N
  set D' := ∑ z in t, single z (1 : Int) with hD'
  -- The auxiliary divisor `D'` is bounded above by `D`.
  have hle : D' <= D := by
    rw [le_def]; rw [Pi.le_def]
    intro w
    simp only [hD', coe_sum, Finset.sum_apply, single_apply, Finset.sum_ite_eq]
    by_cases hw : w in t
    · simp only [hw, if_true]
      have h₁ : D w != 0 := mem_support.mp (htsub (Finset.mem_coe.2 hw))
      have h₂ : (0 : Int) <= D w := by simpa using (le_def.1 h) w
      omega
    · simpa [hw, if_false] using (le_def.1 h) w
  -- A uniform bound on the norms of points in `t`.
  obtain ⟨R₀, hR₀⟩ : exists R₀ : Real, forall z in t, ‖z‖ <= R₀ := t.finite_toSet.isBounded.exists_norm_le
  set K := ∑ z in t, log ‖z‖ with hK
  -- Eventually, `logCounting D' = N * log - K`.
  have hEq : forallᶠ r in atTop, logCounting D' r = (N : Real) * log r - K := by
    filter_upwards [eventually_ge_atTop R₀] with r hr using calc
      logCounting D' r = ∑ c in t, logCounting (single c 1) r := by simp [hD']
       _ = ∑ z in t, (log r - log ‖z‖) := by
        congr! 1 with z hz;
        simpa using logCounting_single_eq_log_sub_const (e := z) (n := 1) ((hR₀ z hz).trans hr)
       _ = (N : Real) * log r - K := by simp [Finset.sum_sub_distrib, hK, htcard]
  -- Combine the bounds into a contradiction with `log → ∞`.
  have hFinal : forallᶠ r in atTop, ((N : Real) - C) * log r <= K := by
    filter_upwards [hEq, eventually_ge_atTop (1 : Real), hC] with r hr₁ hr₂ hr₃
    grind [logCounting_le hle hr₂, norm_eq_abs, abs_of_nonneg, log_nonneg, logCounting_nonneg]
  have hTendsto : Tendsto (fun r => ((N : Real) - C) * log r) atTop atTop :=
    tendsto_log_atTop.const_mul_atTop (sub_pos.mpr hCN')
  obtain ⟨r, hr₁, hr₂⟩ := (hFinal.and (hTendsto.eventually_gt_atTop K)).exists
  linarith

/--
theorem `finite_support_iff_logCounting_isBigO_log` / 定理 `finite_support_iff_logCounting_isBigO_log`

English:
theorem finite_support_iff_logCounting_isBigO_log
  statement: [ProperSpace E]
  proof: ⟨logCounting_isBigO_log_of_finite_support, finite_support_of_logCounting_isBigO_log h⟩

中文:
定理 finite_support_iff_logCounting_isBigO_log
  结论: [命题erSpace E]
  证明: ⟨logCounting_isBigO_log_of_finite_support, finite_support_of_logCounting_isBigO_log h⟩

Depends on / 依赖: finite_support_of_logCounting_isBigO_log, logCounting_isBigO_log_of_finite_support
-/
theorem finite_support_iff_logCounting_isBigO_log [ProperSpace E]
    {D : locallyFinsupp E Int} (h : 0 <= D) :
    D.support.Finite ↔ logCounting D =O[atTop] Real.log :=
  ⟨logCounting_isBigO_log_of_finite_support, finite_support_of_logCounting_isBigO_log h⟩

end Function.locallyFinsuppWithin

namespace ValueDistribution

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Logarithmic Counting Functions for the Poles of a Meromorphic Function
-/

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `logCounting_isBigO_one_iff_analyticOnNhd` / 定理 `logCounting_isBigO_one_iff_analyticOnNhd`

English:
theorem logCounting_isBigO_one_iff_analyticOnNhd
  given: {f : 𝕜 -> E} (h : Meromorphic f)
  proof: by
  simp only [logCounting, reduceDIte]
  rw [← locallyFinsuppWithin.zero_iff_logCounting_bounded (negPart_nonneg _)]; rw [negPart_eq_zero]; rw [← h.meromorphicOn.divisor_of_toMeromorphicNFOn]; rw [(meromorphicNFOn_toMeromorphicNFOn _ _).divisor_nonneg_iff_analyticOnNhd]

中文:
定理 logCounting_isBigO_one_iff_analyticOnNhd
  条件: {f : 𝕜 -> E} (h : Meromorphic f)
  证明: by
  simp only [logCounting, reduceDIte]
  rw [← locallyFinsuppWithin.zero_iff_logCounting_bounded (negPart_nonneg _)]; rw [negPart_eq_zero]; rw [← h.meromorphicOn.divisor_of_toMeromorphicNFOn]; rw [(meromorphicNFOn_toMeromorphicNFOn _ _).divisor_nonneg_iff_analyticOnNhd]

Depends on / 依赖: divisor_nonneg_iff_analyticOnNhd, divisor_of_toMeromorphicNFOn, h.meromorphicOn.divisor_of_toMeromorphicNFOn, locallyFinsuppWithin, locallyFinsuppWithin.zero_iff_logCounting_bounded, logCounting, meromorphicNFOn_toMeromorphicNFOn, meromorphicOn, negPart_eq_zero, negPart_nonneg, reduceDIte, zero_iff_logCounting_bounded
-/
theorem logCounting_isBigO_one_iff_analyticOnNhd {f : 𝕜 -> E} (h : Meromorphic f) :
    logCounting f ⊤ =O[atTop] (1 : Real -> Real) ↔ AnalyticOnNhd 𝕜 (toMeromorphicNFOn f univ) univ := by
  simp only [logCounting, reduceDIte]
  rw [← locallyFinsuppWithin.zero_iff_logCounting_bounded (negPart_nonneg _)]; rw [negPart_eq_zero]; rw [← h.meromorphicOn.divisor_of_toMeromorphicNFOn]; rw [(meromorphicNFOn_toMeromorphicNFOn _ _).divisor_nonneg_iff_analyticOnNhd]

/--
theorem `logCounting_isBigO_log_iff_finite_support` / 定理 `logCounting_isBigO_log_iff_finite_support`

English:
theorem logCounting_isBigO_log_iff_finite_support
  given: {f : 𝕜 -> E}
  proof: by
  rw [logCounting_top]
  exact (locallyFinsuppWithin.finite_support_iff_logCounting_isBigO_log (negPart_nonneg _)).symm

中文:
定理 logCounting_isBigO_log_iff_finite_support
  条件: {f : 𝕜 -> E}
  证明: by
  rw [logCounting_top]
  exact (locallyFinsuppWithin.finite_support_iff_logCounting_isBigO_log (negPart_nonneg _)).symm

Depends on / 依赖: finite_support_iff_logCounting_isBigO_log, locallyFinsuppWithin, locallyFinsuppWithin.finite_support_iff_logCounting_isBigO_log, logCounting_top, negPart_nonneg
-/
theorem logCounting_isBigO_log_iff_finite_support {f : 𝕜 -> E} :
    logCounting f ⊤ =O[atTop] Real.log ↔ (MeromorphicOn.divisor f univ)⁻.support.Finite := by
  rw [logCounting_top]
  exact (locallyFinsuppWithin.finite_support_iff_logCounting_isBigO_log (negPart_nonneg _)).symm

end ValueDistribution
