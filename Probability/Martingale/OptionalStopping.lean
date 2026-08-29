/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Probability.Notation
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.Martingale.Basic

/-! # Optional stopping theorem (fair game theorem)

The optional stopping theorem states that a strongly adapted integrable process `f` is a
submartingale if and only if for all bounded stopping times `τ` and `π` such that `τ ≤ π`, the
stopped value of `f` at `τ` has expectation smaller than its stopped value at `π`.

This file also contains Doob's maximal inequality: given a non-negative submartingale `f`, for all
`ε : ℝ≥0`, we have `ε • μ {ε ≤ f* n} ≤ ∫ ω in {ε ≤ f* n}, f n` where `f * n ω = max_{k ≤ n}, f k ω`.

### Main results

* `MeasureTheory.submartingale_iff_expected_stoppedValue_mono`: the optional stopping theorem.
* `MeasureTheory.Submartingale.stoppedProcess`: the stopped process of a submartingale with
  respect to a stopping time is a submartingale.
* `MeasureTheory.maximal_ineq`: Doob's maximal inequality.

-/

public section


open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration Nat m0} {f : Nat -> Ω -> Real}
  {τ π : Ω -> Nat∞}

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Submartingale.expected_stoppedValue_mono` / 定理 `Submartingale.expected_stoppedValue_mono`

English:
theorem Submartingale.expected_stoppedValue_mono
  statement: {E : Type*} [NormedAddCommGroup E]
  proof: by
  rw [← sub_nonneg]; rw [← integral_sub']; rw [stoppedValue_sub_eq_sum' hle hbdd]
  · simp only [Finset.sum_apply]
    have : forall i, MeasurableSet[𝒢 i] {ω : Ω | τ ω <= i ∧ i < π ω} := by
      intro i
      refine (hτ i).inter ?_
      convert! (hπ i).compl using 1
      ext x
      simp; rfl


中文:
定理 Submartingale.expected_stoppedValue_mono
  结论: {E : 类型} [NormedAddCommGroup E]
  证明: by
  rw [← sub_nonneg]; rw [← integral_sub']; rw [stoppedValue_sub_eq_sum' hle hbdd]
  · simp only [Finset.sum_apply]
    have : forall i, MeasurableSet[𝒢 i] {ω : Ω | τ ω <= i ∧ i < π ω} := by
      intro i
      refine (hτ i).inter ?_
      convert! (hπ i).compl using 1
      ext x
      simp; rfl


Depends on / 依赖: Finset, Finset.sum_apply, Finset.sum_nonneg, MeasurableSet, Nat.le_succ, convert, hf.integrable, hf.setIntegral_le, integrable, integrableOn, integral_finsetSum, integral_indicator, integral_sub, le_succ, setIntegral_le, stoppedValue_sub_eq_sum, sub_nonneg, sum_apply, sum_nonneg
-/
theorem Submartingale.expected_stoppedValue_mono {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] [CompleteSpace E] [PartialOrder E] [IsOrderedAddMonoid E]
    [IsOrderedModule Real E] [ClosedIciTopology E] [SigmaFiniteFiltration μ 𝒢] {f : Nat -> Ω -> E}
    (hf : Submartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) (hπ : IsStoppingTime 𝒢 π) (hle : τ <= π)
    {N : Nat} (hbdd : forall ω, π ω <= N) : μ[stoppedValue f τ] <= μ[stoppedValue f π] := by
  rw [← sub_nonneg]; rw [← integral_sub']; rw [stoppedValue_sub_eq_sum' hle hbdd]
  · simp only [Finset.sum_apply]
    have : forall i, MeasurableSet[𝒢 i] {ω : Ω | τ ω <= i ∧ i < π ω} := by
      intro i
      refine (hτ i).inter ?_
      convert! (hπ i).compl using 1
      ext x
      simp; rfl
    rw [integral_finsetSum]
    · refine Finset.sum_nonneg fun i _ => ?_
      rw [integral_indicator (𝒢.le _ _ (this _))]; rw [integral_sub']; rw [sub_nonneg]
      · exact hf.setIntegral_le (Nat.le_succ i) (this _)
      · exact (hf.integrable _).integrableOn
      · exact (hf.integrable _).integrableOn
    intro i _
    exact Integrable.indicator (Integrable.sub (hf.integrable _) (hf.integrable _))
      (𝒢.le _ _ (this _))
  · exact hf.integrable_stoppedValue hπ hbdd
  · exact hf.integrable_stoppedValue hτ fun ω => le_trans (hle ω) (hbdd ω)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `submartingale_of_expected_stoppedValue_mono` / 定理 `submartingale_of_expected_stoppedValue_mono`

English:
theorem submartingale_of_expected_stoppedValue_mono
  statement: [SigmaFiniteFiltration μ 𝒢]
  proof: by
  refine submartingale_of_setIntegral_le hadp hint fun i j hij s hs => ?_
  classical
  specialize hf (s.piecewise (fun _ => i) fun _ => j) _ (isStoppingTime_piecewise_const hij hs)
    (isStoppingTime_const 𝒢 j) ?_
    ⟨j, fun _ => le_rfl⟩
  · intro ω
    simp only [Set.piecewise, ENat.some_eq_n

中文:
定理 submartingale_of_expected_stoppedValue_mono
  结论: [SigmaFiniteFiltration μ 𝒢]
  证明: by
  refine submartingale_of_setIntegral_le hadp hint fun i j hij s hs => ?_
  classical
  specialize hf (s.piecewise (fun _ => i) fun _ => j) _ (isStoppingTime_piecewise_const hij hs)
    (isStoppingTime_const 𝒢 j) ?_
    ⟨j, fun _ => le_rfl⟩
  · intro ω
    simp only [Set.piecewise, ENat.some_eq_n

Depends on / 依赖: ENat.some_eq_natCast, Set.piecewise, classical, integrableOn, integral_piecewise, isStoppingTime_const, isStoppingTime_piecewise_const, le_rfl, mod_cast, piecewise, s.piecewise, some_eq_natCast, specialize, split_ifs, stoppedValue_const, stoppedValue_piecewise_const, submartingale_of_setIntegral_le
-/
theorem submartingale_of_expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢]
    (hadp : StronglyAdapted 𝒢 f)
    (hint : forall i, Integrable (f i) μ) (hf : forall τ π : Ω -> Nat∞, IsStoppingTime 𝒢 τ -> IsStoppingTime 𝒢 π ->
      τ <= π -> (exists N : Nat, forall ω, π ω <= N) -> μ[stoppedValue f τ] <= μ[stoppedValue f π]) :
    Submartingale f 𝒢 μ := by
  refine submartingale_of_setIntegral_le hadp hint fun i j hij s hs => ?_
  classical
  specialize hf (s.piecewise (fun _ => i) fun _ => j) _ (isStoppingTime_piecewise_const hij hs)
    (isStoppingTime_const 𝒢 j) ?_
    ⟨j, fun _ => le_rfl⟩
  · intro ω
    simp only [Set.piecewise, ENat.some_eq_natCast]
    split_ifs with hω
    · exact mod_cast hij
    · norm_cast
  · rwa [stoppedValue_const, ← ENat.some_eq_natCast, stoppedValue_piecewise_const,
      integral_piecewise (𝒢.le _ _ hs) (hint _).integrableOn (hint _).integrableOn, ←
      integral_add_compl (𝒢.le _ _ hs) (hint j), add_le_add_iff_right] at hf

/--
theorem `submartingale_iff_expected_stoppedValue_mono` / 定理 `submartingale_iff_expected_stoppedValue_mono`

English:
theorem submartingale_iff_expected_stoppedValue_mono
  statement: [SigmaFiniteFiltration μ 𝒢]
  proof: ⟨fun hf _ _ hτ hπ hle ⟨_, hN⟩ => hf.expected_stoppedValue_mono hτ hπ hle hN,
    submartingale_of_expected_stoppedValue_mono hadp hint⟩

中文:
定理 submartingale_iff_expected_stoppedValue_mono
  结论: [SigmaFiniteFiltration μ 𝒢]
  证明: ⟨fun hf _ _ hτ hπ hle ⟨_, hN⟩ => hf.expected_stoppedValue_mono hτ hπ hle hN,
    submartingale_of_expected_stoppedValue_mono hadp hint⟩

Depends on / 依赖: expected_stoppedValue_mono, hf.expected_stoppedValue_mono, submartingale_of_expected_stoppedValue_mono
-/
theorem submartingale_iff_expected_stoppedValue_mono [SigmaFiniteFiltration μ 𝒢]
    (hadp : StronglyAdapted 𝒢 f) (hint : forall i, Integrable (f i) μ) :
    Submartingale f 𝒢 μ ↔ forall τ π : Ω -> Nat∞, IsStoppingTime 𝒢 τ -> IsStoppingTime 𝒢 π ->
      τ <= π -> (exists N : Nat, forall x, π x <= N) -> μ[stoppedValue f τ] <= μ[stoppedValue f π] :=
  ⟨fun hf _ _ hτ hπ hle ⟨_, hN⟩ => hf.expected_stoppedValue_mono hτ hπ hle hN,
    submartingale_of_expected_stoppedValue_mono hadp hint⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Submartingale.stoppedProcess` / 定理 `Submartingale.stoppedProcess`

English:
theorem Submartingale.stoppedProcess
  statement: [SigmaFiniteFiltration μ 𝒢]
  proof: by
  rw [submartingale_iff_expected_stoppedValue_mono]
  · intro σ π hσ hπ hσ_le_π hπ_bdd
    simp_rw [stoppedValue_stoppedProcess]
    obtain ⟨n, hπ_le_n⟩ := hπ_bdd
    have hπ_top ω : π ω != ⊤ := ne_top_of_le_ne_top (by simp) (hπ_le_n ω)
    have hσ_top ω : σ ω != ⊤ := ne_top_of_le_ne_top (hπ_top 

中文:
定理 Submartingale.stoppedProcess
  结论: [SigmaFiniteFiltration μ 𝒢]
  证明: by
  rw [submartingale_iff_expected_stoppedValue_mono]
  · intro σ π hσ hπ hσ_le_π hπ_bdd
    simp_rw [stoppedValue_stoppedProcess]
    obtain ⟨n, hπ_le_n⟩ := hπ_bdd
    have hπ_top ω : π ω != ⊤ := ne_top_of_le_ne_top (by simp) (hπ_le_n ω)
    have hσ_top ω : σ ω != ⊤ := ne_top_of_le_ne_top (hπ_top 
-/
protected theorem Submartingale.stoppedProcess [SigmaFiniteFiltration μ 𝒢]
    (h : Submartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ) :
    Submartingale (stoppedProcess f τ) 𝒢 μ := by
  rw [submartingale_iff_expected_stoppedValue_mono]
  · intro σ π hσ hπ hσ_le_π hπ_bdd
    simp_rw [stoppedValue_stoppedProcess]
    obtain ⟨n, hπ_le_n⟩ := hπ_bdd
    have hπ_top ω : π ω != ⊤ := ne_top_of_le_ne_top (by simp) (hπ_le_n ω)
    have hσ_top ω : σ ω != ⊤ := ne_top_of_le_ne_top (hπ_top ω) (hσ_le_π ω)
    simp only [ne_eq, hσ_top, not_false_eq_true, ↓reduceIte, hπ_top, ge_iff_le]
    exact h.expected_stoppedValue_mono (hσ.min hτ) (hπ.min hτ)
      (fun ω => min_le_min (hσ_le_π ω) le_rfl) fun ω => (min_le_left _ _).trans (hπ_le_n ω)
  · exact StronglyAdapted.stoppedProcess_of_discrete h.stronglyAdapted hτ
  · exact fun i =>
      h.integrable_stoppedValue ((isStoppingTime_const _ i).min hτ) fun ω => min_le_left _ _

section Maximal

open Finset

set_option backward.isDefEq.respectTransparency false in
/--
theorem `smul_le_stoppedValue_hittingBtwn` / 定理 `smul_le_stoppedValue_hittingBtwn`

English:
theorem smul_le_stoppedValue_hittingBtwn
  statement: [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) {ε : Real>=0}
  proof: by
  have : forall ω, ((ε : Real) <= (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) ->
      (ε : Real) <= stoppedValue f (fun ω => (hittingBtwn f {y : Real | ε <= y} 0 n ω : Nat)) ω := by
    intro x hx
    simp_rw [le_sup'_iff, mem_range, Nat.lt_succ_iff] at hx
    refine stoppedValue

中文:
定理 smul_le_stoppedValue_hittingBtwn
  结论: [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) {ε : 实数>=0}
  证明: by
  have : forall ω, ((ε : Real) <= (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) ->
      (ε : Real) <= stoppedValue f (fun ω => (hittingBtwn f {y : Real | ε <= y} 0 n ω : Nat)) ω := by
    intro x hx
    simp_rw [le_sup'_iff, mem_range, Nat.lt_succ_iff] at hx
    refine stoppedValue

Depends on / 依赖: Nat.lt_succ_iff, Set.mem_Icc, Set.mem_ofPred_eq, _iff, hittingBtwn, le_sup, lt_succ_iff, measurableSet_le, measurable_const, measurable_range, mem_Icc, mem_ofPred_eq, mem_range, nonempty_range_add_one, setIntegral_ge_of_const_le_real, simp_rw, stoppedValue, stoppedValue_hittingBtwn_mem, true_and, zero_le
-/
theorem smul_le_stoppedValue_hittingBtwn [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) {ε : Real>=0}
    (n : Nat) : ε • μ {ω | (ε : Real) <= (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} <=
    ENNReal.ofReal
      (∫ ω in {ω | (ε : Real) <= (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
      stoppedValue f (fun ω => (hittingBtwn f {y : Real | ε <= y} 0 n ω : Nat)) ω ∂μ) := by
  have : forall ω, ((ε : Real) <= (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) ->
      (ε : Real) <= stoppedValue f (fun ω => (hittingBtwn f {y : Real | ε <= y} 0 n ω : Nat)) ω := by
    intro x hx
    simp_rw [le_sup'_iff, mem_range, Nat.lt_succ_iff] at hx
    refine stoppedValue_hittingBtwn_mem ?_
    simp only [Set.mem_Icc, zero_le, true_and, Set.mem_ofPred_eq]
    exact
      let ⟨j, hj₁, hj₂⟩ := hx
      ⟨j, hj₁, hj₂⟩
  have h := setIntegral_ge_of_const_le_real (measurableSet_le measurable_const
    (measurable_range_sup'' fun n _ => (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)))
      (measure_ne_top _ _) this (Integrable.integrableOn (hsub.integrable_stoppedValue
        (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
        (mod_cast hittingBtwn_le)))
  rw [ENNReal.le_ofReal_iff_toReal_le]; rw [ENNReal.toReal_smul]
  · exact h
  · exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  · exact le_trans (mul_nonneg ε.coe_nonneg ENNReal.toReal_nonneg) h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `maximal_ineq` / 定理 `maximal_ineq`

English:
theorem maximal_ineq
  statement: [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 <= f) {ε : Real>=0}
  proof: by
  suffices ε • μ {ω | (ε : Real) <= (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} +
      ENNReal.ofReal
        (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
          f n ω ∂μ) <=
      ENNReal.ofReal (μ[f n]) by
    have hadd : ENNReal.ofReal (∫ 

中文:
定理 maximal_ineq
  结论: [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 <= f) {ε : 实数>=0}
  证明: by
  suffices ε • μ {ω | (ε : Real) <= (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} +
      ENNReal.ofReal
        (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
          f n ω ∂μ) <=
      ENNReal.ofReal (μ[f n]) by
    have hadd : ENNReal.ofReal (∫ 

Depends on / 依赖: ENNReal, ENNReal.ofReal, nonempty_range_add_one, ofReal
-/
theorem maximal_ineq [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 <= f) {ε : Real>=0}
    (n : Nat) : ε * μ {ω | (ε : Real) <= (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} <=
    ENNReal.ofReal
      (∫ ω in {ω | (ε : Real) <= (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
        f n ω ∂μ) := by
  suffices ε • μ {ω | (ε : Real) <= (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω} +
      ENNReal.ofReal
        (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
          f n ω ∂μ) <=
      ENNReal.ofReal (μ[f n]) by
    have hadd : ENNReal.ofReal (∫ ω, f n ω ∂μ) =
      ENNReal.ofReal
        (∫ ω in {ω | ε <= (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω}, f n ω ∂μ) +
      ENNReal.ofReal
        (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
          f n ω ∂μ) := by
      rw [← ENNReal.ofReal_add]; rw [← setIntegral_union]
      · rw [← setIntegral_univ]
        convert! rfl
        ext ω
        change (ε : Real) <= _ ∨ _ < (ε : Real) ↔ _
        simp only [le_or_gt, Set.mem_univ]
      · grind
      · exact measurableSet_lt (measurable_range_sup'' fun n _ =>
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)) measurable_const
      exacts [(hsub.integrable _).integrableOn, (hsub.integrable _).integrableOn,
        integral_nonneg (hnonneg _), integral_nonneg (hnonneg _)]
    rwa [hadd, ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top] at this
  calc
    _ <= ENNReal.ofReal
          (∫ ω in {ω | (ε : Real) <= (range (n + 1)).sup' nonempty_range_add_one fun k => f k ω},
            stoppedValue f (fun ω => (hittingBtwn f {y : Real | ε <= y} 0 n ω : Nat)) ω ∂μ) +
        ENNReal.ofReal
          (∫ ω in {ω | ((range (n + 1)).sup' nonempty_range_add_one fun k => f k ω) < ε},
            stoppedValue f (fun ω => (hittingBtwn f {y : Real | ε <= y} 0 n ω : Nat)) ω ∂μ) := by
      gcongr with ω hω
      · exact smul_le_stoppedValue_hittingBtwn hsub n
      · exact (hsub.integrable n).integrableOn
      · refine Integrable.integrableOn ?_
        refine hsub.integrable_stoppedValue ?_ (fun ω => mod_cast hittingBtwn_le ω)
        exact hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
      · exact nullMeasurableSet_lt (measurable_range_sup'' fun n _ =>
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)).aemeasurable aemeasurable_const
      rw [Set.mem_ofPred_eq] at hω
      have : hittingBtwn f {y : Real | ε <= y} 0 n ω = n := by
        simp only [hittingBtwn, Set.mem_ofPred_eq, ite_eq_right_iff, forall_exists_index, and_imp]
        intro m hm hεm
        exact False.elim
          ((not_le.2 hω) ((le_sup'_iff _).2 ⟨m, mem_range.2 (Nat.lt_succ_of_le hm.2), hεm⟩))
      simp only [stoppedValue, this, ge_iff_le]
      refine le_of_eq ?_
      congr
    _ = ENNReal.ofReal
        (∫ ω, stoppedValue f (fun ω => (hittingBtwn f {y : Real | ε <= y} 0 n ω : Nat)) ω ∂μ) := by
      rw [← ENNReal.ofReal_add]; rw [← setIntegral_union]
      · rw [← setIntegral_univ (μ := μ)]
        convert! rfl
        ext ω
        change _ ↔ (ε : Real) <= _ ∨ _ < (ε : Real)
        simp only [le_or_gt, Set.mem_univ]
      · grind
      · exact measurableSet_lt (measurable_range_sup'' fun n _ =>
          (hsub.stronglyMeasurable n).measurable.le (𝒢.le n)) measurable_const
      · exact Integrable.integrableOn (hsub.integrable_stoppedValue
          (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
          (fun ω => mod_cast hittingBtwn_le ω))
      · exact Integrable.integrableOn (hsub.integrable_stoppedValue
          (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
          (fun ω => mod_cast hittingBtwn_le ω))
      exacts [integral_nonneg fun x => hnonneg _ _, integral_nonneg fun x => hnonneg _ _]
    _ <= ENNReal.ofReal (μ[f n]) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← stoppedValue_const f n]
      refine hsub.expected_stoppedValue_mono
        (hsub.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici)
        (isStoppingTime_const _ _) (fun ω => ?_) (fun _ => mod_cast le_rfl)
      simp [hittingBtwn_le]

end Maximal

end MeasureTheory
