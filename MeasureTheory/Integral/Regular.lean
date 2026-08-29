/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.UrysohnsLemma

/-!
# Integrals of continuous functions with respect to regular measures

When a measure is regular, one may express the measure of compact sets and of open sets
in terms of the integral of continuous functions equal to 1 on the compact set, or to 0 outside
of the open set respectively.
-/

public section

open Filter Set MeasureTheory Measure

/--
lemma `IsCompact.measure_eq_biInf_integral_hasCompactSupport` / 引理 `IsCompact.measure_eq_biInf_integral_hasCompactSupport`

English:
lemma IsCompact.measure_eq_biInf_integral_hasCompactSupport
  proof: by
  apply le_antisymm
  · simp only [le_iInf_iff]
    intro f f_cont f_comp fk f_nonneg
    apply (f_cont.integrable_of_hasCompactSupport f_comp).measure_le_integral
    · exact Eventually.of_forall f_nonneg
    · exact fun x hx => by simp [fk hx]
  · apply le_of_forall_gt (fun r hr => ?_)
    simp

中文:
引理 是紧集.measure_eq_biInf_integral_hasCompactSupport
  证明: by
  apply le_antisymm
  · simp only [le_iInf_iff]
    intro f f_cont f_comp fk f_nonneg
    apply (f_cont.integrable_of_hasCompactSupport f_comp).measure_le_integral
    · exact Eventually.of_forall f_nonneg
    · exact fun x hx => by simp [fk hx]
  · apply le_of_forall_gt (fun r hr => ?_)
    simp

Depends on / 依赖: Eventually, Eventually.of_forall, IsOpen, U_open, exists_isOpen_lt_of_lt, exists_prop, f_comp, f_cont, f_cont.integrable_of_hasCompactSupport, f_nonneg, f_range, hk.exists_isOpen_lt_of_lt, iInf_lt_iff, integrable_of_hasCompactSupport, le_antisymm, le_iInf_iff, le_of_forall_gt, measure_le_integral, mu_U, of_forall
-/
lemma IsCompact.measure_eq_biInf_integral_hasCompactSupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : Set X} (hk : IsCompact k)
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [InnerRegularCompactLTTop μ]
    [LocallyCompactSpace X] [RegularSpace X] :
    μ k = ⨅ (f : X -> Real) (_ : Continuous f) (_ : HasCompactSupport f) (_ : EqOn f 1 k)
      (_ : 0 <= f), ENNReal.ofReal (∫ x, f x ∂μ) := by
  apply le_antisymm
  · simp only [le_iInf_iff]
    intro f f_cont f_comp fk f_nonneg
    apply (f_cont.integrable_of_hasCompactSupport f_comp).measure_le_integral
    · exact Eventually.of_forall f_nonneg
    · exact fun x hx => by simp [fk hx]
  · apply le_of_forall_gt (fun r hr => ?_)
    simp only [iInf_lt_iff, exists_prop]
    obtain ⟨U, kU, U_open, mu_U⟩ : exists U, k subseteq U ∧ IsOpen U ∧ μ U < r :=
      hk.exists_isOpen_lt_of_lt r hr
    obtain ⟨⟨f, f_cont⟩, fk, fU, f_comp, f_range⟩ : exists (f : C(X, Real)), EqOn f 1 k ∧ EqOn f 0 Uᶜ
        ∧ HasCompactSupport f ∧ forall (x : X), f x in Icc 0 1 := exists_continuous_one_zero_of_isCompact
      hk U_open.isClosed_compl (disjoint_compl_right_iff_subset.mpr kU)
    refine ⟨f, f_cont, f_comp, fk, fun x => (f_range x).1, ?_⟩
    exact (integral_le_measure (fun x _hx => (f_range x).2) (fun x hx => (fU hx).le)).trans_lt mu_U

/--
lemma `IsOpen.measure_eq_biSup_integral_continuous` / 引理 `IsOpen.measure_eq_biSup_integral_continuous`

English:
lemma IsOpen.measure_eq_biSup_integral_continuous
  proof: by
  apply le_antisymm
  · apply le_of_forall_lt (fun r hr => ?_)
    simp only [lt_iSup_iff, exists_prop]
    obtain ⟨K, KU, K_comp, hK⟩ : exists K subseteq U, IsCompact K ∧ r < μ K :=
      MeasurableSet.exists_lt_isCompact_of_ne_top hU.measurableSet (by simp) hr
    obtain ⟨⟨f, f_cont⟩, fU, fK, f

中文:
引理 是开集.measure_eq_biSup_integral_continuous
  证明: by
  apply le_antisymm
  · apply le_of_forall_lt (fun r hr => ?_)
    simp only [lt_iSup_iff, exists_prop]
    obtain ⟨K, KU, K_comp, hK⟩ : exists K subseteq U, IsCompact K ∧ r < μ K :=
      MeasurableSet.exists_lt_isCompact_of_ne_top hU.measurableSet (by simp) hr
    obtain ⟨⟨f, f_cont⟩, fU, fK, f

Depends on / 依赖: IsCompact, K_comp, K_comp.isClosed, MeasurableSet, MeasurableSet.exists_lt_isCompact_of_ne_top, disjoint_compl_left_iff_subset, disjoint_compl_left_iff_subset.mpr, exists_continuous_zero_one_of_isClosed, exists_lt_isCompact_of_ne_top, exists_prop, f_cont, f_range, hU.isClosed_compl, hU.measurableSet, isClosed, isClosed_compl, le_antisymm, le_of_forall_lt, lt_iSup_iff, measurableSet
-/
lemma IsOpen.measure_eq_biSup_integral_continuous
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
    {U : Set X} (hU : IsOpen U)
    (μ : Measure X) [IsFiniteMeasure μ] [InnerRegularCompactLTTop μ] [NormalSpace X] :
    μ U = ⨆ (f : X -> Real) (_ : Continuous f) (_ : EqOn f 0 Uᶜ) (_ : 0 <= f) (_ : f <= 1),
      ENNReal.ofReal (∫ x, f x ∂μ) := by
  apply le_antisymm
  · apply le_of_forall_lt (fun r hr => ?_)
    simp only [lt_iSup_iff, exists_prop]
    obtain ⟨K, KU, K_comp, hK⟩ : exists K subseteq U, IsCompact K ∧ r < μ K :=
      MeasurableSet.exists_lt_isCompact_of_ne_top hU.measurableSet (by simp) hr
    obtain ⟨⟨f, f_cont⟩, fU, fK, f_range⟩ : exists (f : C(X, Real)), EqOn f 0 Uᶜ ∧ EqOn f 1 K
        ∧ forall (x : X), f x in Icc 0 1 := exists_continuous_zero_one_of_isClosed
      hU.isClosed_compl K_comp.isClosed (disjoint_compl_left_iff_subset.mpr KU)
    refine ⟨f, f_cont, fU, fun x => (f_range x).1, fun x => (f_range x).2, ?_⟩
    apply hK.trans_le
    apply Integrable.measure_le_integral
    · apply Integrable.of_mem_Icc 0 1 f_cont.aemeasurable
      filter_upwards [] with x using f_range x
    · filter_upwards [] with x using (f_range x).1
    · intro x hx
      apply Eq.ge
      exact fK hx
  · simp only [iSup_le_iff]
    intro f f_cont fU f_nonneg f_le
    exact integral_le_measure (fun x hx => f_le x) (fun x hx => le_of_eq (fU hx))
