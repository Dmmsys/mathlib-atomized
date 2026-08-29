/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.Holder

/-!
# Pull-out property of the conditional expectation

Let `Ω` be endowed with a measurable space structure `mΩ`, and let `m : MeasurableSpace Ω` such that
`m ≤ mΩ`. Let `μ` be a measure over `Ω`. Let `B : F →L[ℝ] E →L[ℝ] G` a continuous bilinear map,
`f : Ω → F` and `g : Ω → E` such that `fun ω ↦ B (f ω) (g ω)` is integrable, `g` is integrable
and `f` is `AEStronglyMeasurable` with respect to `m`. The **pull-out** property of the conditional
expectation states that almost surely, `μ[B f g|m] = B f μ[g|m]`.

We specialize this statement to the cases where `B` is scalar multiplication and multiplication.

## Main statements

* `condExp_bilin_of_aestronglyMeasurable_left`: The pull-out property of the conditional
  expectation: almost surely, `μ[B f g|m] = B f μ[g|m]`.
* `condExp_smul_of_aestronglyMeasurable_left`: The pull-out property of the conditional
  expectation: almost surely, `μ[f • g|m] = f • μ[g|m]`.
* `condExp_mul_of_aestronglyMeasurable_left`: The pull-out property of the conditional
  expectation: almost surely, `μ[f * g|m] = f * μ[g|m]`.

## Tags

conditional expectation, pull-out, bilinear map
-/

public section


open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F] [NormedAddCommGroup G] [NormedSpace Real G]
  [CompleteSpace G] (B : F ->L[Real] E ->L[Real] G)

/--
theorem `condExp_stronglyMeasurable_simpleFunc_bilin` / 定理 `condExp_stronglyMeasurable_simpleFunc_bilin`

English:
theorem condExp_stronglyMeasurable_simpleFunc_bilin
  statement: [CompleteSpace E]
  proof: by
  have : forall (s c) (f : Ω -> E),
      (fun ω => B (Set.indicator s (Function.const Ω c) ω) (f ω)) =
        s.indicator (fun ω => B c (f ω)) := by
    intro s c f
    ext ω
    by_cases hω : ω in s <;> simp [hω]
  apply @SimpleFunc.induction _ _ m _ (fun f => _)
    (fun c s hs => ?_) (fun g₁ g₂ _ h_eq₁ h_eq₂ => ?_) f
  · simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    rw [this]; rw [this]
    refine (condExp_indicator ((B c).integrable_comp hg) hs).trans ?_
    filter_upwards [(B c).comp_condExp_comm hg (m := m)] with ω hω
    simp only [Function.comp_apply] at hω
    simp only [Set.indicator, hω, Function.comp_def]
  · have h_add := @SimpleFunc.coe_add _ _ m _ g₁ g₂
    calc
      μ[fun ω => B (g₁ ω + g₂ ω) (g ω) | m] =ᵐ[μ]
          μ[fun ω => B (g₁ ω) (g ω) | m] + μ[fun ω => B (g₂ ω) (g ω) | m] := by
        simp_rw [B.map_add]
        obtain ⟨C₁, hC₁⟩ := @SimpleFunc.exists_forall_norm_le _ _ m _ g₁
        obtain ⟨C₂, hC₂⟩ := @SimpleFunc.exists_forall_norm_le _ _ m _ g₂
        exact condExp_add
          (B.integrable_of_bilin_of_bdd_left C₁ (g₁.stronglyMeasurable.mono hm).aestronglyMeasurable
            (ae_of_all _ hC₁) hg)
          (B.integrable_of_bilin_of_bdd_left C₂ (g₂.stronglyMeasurable.mono hm).aestronglyMeasurable
            (ae_of_all _ hC₂) hg) m
      _ =ᵐ[μ] fun ω => B (g₁ ω) (μ[g | m] ω) + B (g₂ ω) (μ[g | m] ω) := EventuallyEq.add h_eq₁ h_eq₂
      _ =ᵐ[μ] fun ω => B ((g₁ + g₂) ω) (μ[g | m] ω) := by simp

中文:
定理 condExp_stronglyMeasurable_simpleFunc_bilin
  结论: [完备空间 E]
  证明: by
  have : forall (s c) (f : Ω -> E),
      (fun ω => B (Set.indicator s (Function.const Ω c) ω) (f ω)) =
        s.indicator (fun ω => B c (f ω)) := by
    intro s c f
    ext ω
    by_cases hω : ω in s <;> simp [hω]
  apply @SimpleFunc.induction _ _ m _ (fun f => _)
    (fun c s hs => ?_) (fun g₁ g₂ _ h_eq₁ h_eq₂ => ?_) f
  · simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    rw [this]; rw [this]
    refine (condExp_indicator ((B c).integrable_comp hg) hs).trans ?_
    filter_upwards [(B c).comp_condExp_comm hg (m := m)] with ω hω
    simp only [Function.comp_apply] at hω
    simp only [Set.indicator, hω, Function.comp_def]
  · have h_add := @SimpleFunc.coe_add _ _ m _ g₁ g₂
    calc
      μ[fun ω => B (g₁ ω + g₂ ω) (g ω) | m] =ᵐ[μ]
          μ[fun ω => B (g₁ ω) (g ω) | m] + μ[fun ω => B (g₂ ω) (g ω) | m] := by
        simp_rw [B.map_add]
        obtain ⟨C₁, hC₁⟩ := @SimpleFunc.exists_forall_norm_le _ _ m _ g₁
        obtain ⟨C₂, hC₂⟩ := @SimpleFunc.exists_forall_norm_le _ _ m _ g₂
        exact condExp_add
          (B.integrable_of_bilin_of_bdd_left C₁ (g₁.stronglyMeasurable.mono hm).aestronglyMeasurable
            (ae_of_all _ hC₁) hg)
          (B.integrable_of_bilin_of_bdd_left C₂ (g₂.stronglyMeasurable.mono hm).aestronglyMeasurable
            (ae_of_all _ hC₂) hg) m
      _ =ᵐ[μ] fun ω => B (g₁ ω) (μ[g | m] ω) + B (g₂ ω) (μ[g | m] ω) := EventuallyEq.add h_eq₁ h_eq₂
      _ =ᵐ[μ] fun ω => B ((g₁ + g₂) ω) (μ[g | m] ω) := by simp

Depends on / 依赖: Function, Function.const, Set.indicator, Set.piecewise_eq_indicator, SimpleFunc, SimpleFunc.coe_const, SimpleFunc.coe_piecewise, SimpleFunc.coe_zero, SimpleFunc.const_zero, SimpleFunc.induction, coe_const, coe_piecewise, coe_zero, condExp_indicator, const_zero, indicator, integrable_comp, of_surjective, piecewise_eq_indicator, s.indicator
-/
theorem condExp_stronglyMeasurable_simpleFunc_bilin [CompleteSpace E]
    (hm : m <= mΩ) (f : @SimpleFunc Ω m F) {g : Ω -> E} (hg : Integrable g μ) :
    μ[fun ω => B (f ω) (g ω) | m] =ᵐ[μ] fun ω => B (f ω) (μ[g | m] ω) := by
  have : forall (s c) (f : Ω -> E),
      (fun ω => B (Set.indicator s (Function.const Ω c) ω) (f ω)) =
        s.indicator (fun ω => B c (f ω)) := by
    intro s c f
    ext ω
    by_cases hω : ω in s <;> simp [hω]
  apply @SimpleFunc.induction _ _ m _ (fun f => _)
    (fun c s hs => ?_) (fun g₁ g₂ _ h_eq₁ h_eq₂ => ?_) f
  · simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    rw [this]; rw [this]
    refine (condExp_indicator ((B c).integrable_comp hg) hs).trans ?_
    filter_upwards [(B c).comp_condExp_comm hg (m := m)] with ω hω
    simp only [Function.comp_apply] at hω
    simp only [Set.indicator, hω, Function.comp_def]
  · have h_add := @SimpleFunc.coe_add _ _ m _ g₁ g₂
    calc
      μ[fun ω => B (g₁ ω + g₂ ω) (g ω) | m] =ᵐ[μ]
          μ[fun ω => B (g₁ ω) (g ω) | m] + μ[fun ω => B (g₂ ω) (g ω) | m] := by
        simp_rw [B.map_add]
        obtain ⟨C₁, hC₁⟩ := @SimpleFunc.exists_forall_norm_le _ _ m _ g₁
        obtain ⟨C₂, hC₂⟩ := @SimpleFunc.exists_forall_norm_le _ _ m _ g₂
        exact condExp_add
          (B.integrable_of_bilin_of_bdd_left C₁ (g₁.stronglyMeasurable.mono hm).aestronglyMeasurable
            (ae_of_all _ hC₁) hg)
          (B.integrable_of_bilin_of_bdd_left C₂ (g₂.stronglyMeasurable.mono hm).aestronglyMeasurable
            (ae_of_all _ hC₂) hg) m
      _ =ᵐ[μ] fun ω => B (g₁ ω) (μ[g | m] ω) + B (g₂ ω) (μ[g | m] ω) := EventuallyEq.add h_eq₁ h_eq₂
      _ =ᵐ[μ] fun ω => B ((g₁ + g₂) ω) (μ[g | m] ω) := by simp

/--
theorem `condExp_stronglyMeasurable_bilin_of_bound` / 定理 `condExp_stronglyMeasurable_bilin_of_bound`

English:
theorem condExp_stronglyMeasurable_bilin_of_bound
  statement: [CompleteSpace E]
  proof: by
  let fs := hf.approxBounded c
  have hfs_tendsto : forallᵐ ω ∂μ, Tendsto (fs · ω) atTop (𝓝 (f ω)) :=
    hf.tendsto_approxBounded_ae hf_bound
  by_cases hμ : μ = 0
  · simp only [hμ, ae_zero]; norm_cast
  have : (ae μ).NeBot := ae_neBot.2 hμ
  have hc : 0 <= c := by
    rcases hf_bound.exists with ⟨_, h⟩
    exact (norm_nonneg _).trans h
  have hfs_bound : forall n ω, ‖fs n ω‖ <= c := hf.norm_approxBounded_le hc
  have : μ[fun ω => B (f ω) (μ[g | m] ω) | m] = fun ω => B (f ω) (μ[g | m] ω) := by
    refine condExp_of_stronglyMeasurable hm ?_ ?_
    · exact Continuous.comp_stronglyMeasurable (g := (fun z : F × E => B z.1 z.2)) (by fun_prop)
        (hf.prodMk stronglyMeasurable_condExp)
    · exact B.integrable_of_bilin_of_bdd_left c (hf.mono hm).aestronglyMeasurable hf_bound
        integrable_condExp
  rw [← this]
  refine tendsto_condExp_unique (fun n ω => B (fs n ω) (g ω))
    (fun n ω => B (fs n ω) (μ[g | m] ω)) (fun ω => B (f ω) (g ω))
    (fun ω => B (f ω) (μ[g | m] ω)) ?_ ?_ ?_ ?_ (‖B‖ * c * ‖g ·‖) ?_ (‖B‖ * c * ‖(μ[g | m]) ·‖)
    ?_ ?_ ?_ ?_
  · exact fun n => B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n) hg
  · exact fun n => B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n)
      integrable_condExp
  · filter_upwards [hfs_tendsto] with ω hω
    exact ((by fun_prop : Continuous (fun x => B x (g ω))).tendsto (f ω)).comp hω
  · filter_upwards [hfs_tendsto] with ω hω
    exact ((by fun_prop : Continuous (fun x => B x (μ[g | m] ω))).tendsto (f ω)).comp hω
  · exact hg.norm.const_mul _
  · fun_prop
  · refine fun n => Eventually.of_forall fun _ => ?_
    grw [B.le_opNorm₂, hfs_bound]
  · refine fun n => Eventually.of_forall fun _ => ?_
    grw [B.le_opNorm₂, hfs_bound]
  · intro n
    refine (condExp_stronglyMeasurable_simpleFunc_bilin B hm _ hg).trans ?_
    nth_rw 2 [condExp_of_stronglyMeasurable hm]
    · exact Continuous.comp_stronglyMeasurable (g := (fun z : F × E => B z.1 z.2)) (by fun_prop)
        ((fs n).stronglyMeasurable.prodMk stronglyMeasurable_condExp)
    exact B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n)
      integrable_condExp

中文:
定理 condExp_stronglyMeasurable_bilin_of_bound
  结论: [完备空间 E]
  证明: by
  let fs := hf.approxBounded c
  have hfs_tendsto : forallᵐ ω ∂μ, Tendsto (fs · ω) atTop (𝓝 (f ω)) :=
    hf.tendsto_approxBounded_ae hf_bound
  by_cases hμ : μ = 0
  · simp only [hμ, ae_zero]; norm_cast
  have : (ae μ).NeBot := ae_neBot.2 hμ
  have hc : 0 <= c := by
    rcases hf_bound.exists with ⟨_, h⟩
    exact (norm_nonneg _).trans h
  have hfs_bound : forall n ω, ‖fs n ω‖ <= c := hf.norm_approxBounded_le hc
  have : μ[fun ω => B (f ω) (μ[g | m] ω) | m] = fun ω => B (f ω) (μ[g | m] ω) := by
    refine condExp_of_stronglyMeasurable hm ?_ ?_
    · exact Continuous.comp_stronglyMeasurable (g := (fun z : F × E => B z.1 z.2)) (by fun_prop)
        (hf.prodMk stronglyMeasurable_condExp)
    · exact B.integrable_of_bilin_of_bdd_left c (hf.mono hm).aestronglyMeasurable hf_bound
        integrable_condExp
  rw [← this]
  refine tendsto_condExp_unique (fun n ω => B (fs n ω) (g ω))
    (fun n ω => B (fs n ω) (μ[g | m] ω)) (fun ω => B (f ω) (g ω))
    (fun ω => B (f ω) (μ[g | m] ω)) ?_ ?_ ?_ ?_ (‖B‖ * c * ‖g ·‖) ?_ (‖B‖ * c * ‖(μ[g | m]) ·‖)
    ?_ ?_ ?_ ?_
  · exact fun n => B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n) hg
  · exact fun n => B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n)
      integrable_condExp
  · filter_upwards [hfs_tendsto] with ω hω
    exact ((by fun_prop : Continuous (fun x => B x (g ω))).tendsto (f ω)).comp hω
  · filter_upwards [hfs_tendsto] with ω hω
    exact ((by fun_prop : Continuous (fun x => B x (μ[g | m] ω))).tendsto (f ω)).comp hω
  · exact hg.norm.const_mul _
  · fun_prop
  · refine fun n => Eventually.of_forall fun _ => ?_
    grw [B.le_opNorm₂, hfs_bound]
  · refine fun n => Eventually.of_forall fun _ => ?_
    grw [B.le_opNorm₂, hfs_bound]
  · intro n
    refine (condExp_stronglyMeasurable_simpleFunc_bilin B hm _ hg).trans ?_
    nth_rw 2 [condExp_of_stronglyMeasurable hm]
    · exact Continuous.comp_stronglyMeasurable (g := (fun z : F × E => B z.1 z.2)) (by fun_prop)
        ((fs n).stronglyMeasurable.prodMk stronglyMeasurable_condExp)
    exact B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n)
      integrable_condExp

Depends on / 依赖: Tendsto, ae_neBot, ae_zero, approxBounded, condExp_of_strong, hf.approxBounded, hf.norm_approxBounded_le, hf.tendsto_approxBounded_ae, hf_bound, hf_bound.exists, hfs_bound, hfs_tendsto, norm_approxBounded_le, norm_nonneg, tendsto_approxBounded_ae
-/
theorem condExp_stronglyMeasurable_bilin_of_bound [CompleteSpace E]
    (hm : m <= mΩ) [IsFiniteMeasure μ] {f : Ω -> F} {g : Ω -> E} (hf : StronglyMeasurable[m] f)
    (hg : Integrable g μ) (c : Real) (hf_bound : forallᵐ ω ∂μ, ‖f ω‖ <= c) :
    μ[fun ω => B (f ω) (g ω) | m] =ᵐ[μ] fun ω => B (f ω) (μ[g | m] ω) := by
  let fs := hf.approxBounded c
  have hfs_tendsto : forallᵐ ω ∂μ, Tendsto (fs · ω) atTop (𝓝 (f ω)) :=
    hf.tendsto_approxBounded_ae hf_bound
  by_cases hμ : μ = 0
  · simp only [hμ, ae_zero]; norm_cast
  have : (ae μ).NeBot := ae_neBot.2 hμ
  have hc : 0 <= c := by
    rcases hf_bound.exists with ⟨_, h⟩
    exact (norm_nonneg _).trans h
  have hfs_bound : forall n ω, ‖fs n ω‖ <= c := hf.norm_approxBounded_le hc
  have : μ[fun ω => B (f ω) (μ[g | m] ω) | m] = fun ω => B (f ω) (μ[g | m] ω) := by
    refine condExp_of_stronglyMeasurable hm ?_ ?_
    · exact Continuous.comp_stronglyMeasurable (g := (fun z : F × E => B z.1 z.2)) (by fun_prop)
        (hf.prodMk stronglyMeasurable_condExp)
    · exact B.integrable_of_bilin_of_bdd_left c (hf.mono hm).aestronglyMeasurable hf_bound
        integrable_condExp
  rw [← this]
  refine tendsto_condExp_unique (fun n ω => B (fs n ω) (g ω))
    (fun n ω => B (fs n ω) (μ[g | m] ω)) (fun ω => B (f ω) (g ω))
    (fun ω => B (f ω) (μ[g | m] ω)) ?_ ?_ ?_ ?_ (‖B‖ * c * ‖g ·‖) ?_ (‖B‖ * c * ‖(μ[g | m]) ·‖)
    ?_ ?_ ?_ ?_
  · exact fun n => B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n) hg
  · exact fun n => B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n)
      integrable_condExp
  · filter_upwards [hfs_tendsto] with ω hω
    exact ((by fun_prop : Continuous (fun x => B x (g ω))).tendsto (f ω)).comp hω
  · filter_upwards [hfs_tendsto] with ω hω
    exact ((by fun_prop : Continuous (fun x => B x (μ[g | m] ω))).tendsto (f ω)).comp hω
  · exact hg.norm.const_mul _
  · fun_prop
  · refine fun n => Eventually.of_forall fun _ => ?_
    grw [B.le_opNorm₂, hfs_bound]
  · refine fun n => Eventually.of_forall fun _ => ?_
    grw [B.le_opNorm₂, hfs_bound]
  · intro n
    refine (condExp_stronglyMeasurable_simpleFunc_bilin B hm _ hg).trans ?_
    nth_rw 2 [condExp_of_stronglyMeasurable hm]
    · exact Continuous.comp_stronglyMeasurable (g := (fun z : F × E => B z.1 z.2)) (by fun_prop)
        ((fs n).stronglyMeasurable.prodMk stronglyMeasurable_condExp)
    exact B.integrable_of_bilin_of_bdd_left c
      ((fs n).stronglyMeasurable.mono hm).aestronglyMeasurable (ae_of_all _ <| hfs_bound n)
      integrable_condExp

/--
theorem `condExp_aestronglyMeasurable_bilin_of_bound` / 定理 `condExp_aestronglyMeasurable_bilin_of_bound`

English:
theorem condExp_aestronglyMeasurable_bilin_of_bound
  statement: [CompleteSpace E]
  proof: calc
  μ[fun ω => B (f ω) (g ω) | m]
  _ =ᵐ[μ] μ[fun ω => B (hf.mk f ω) (g ω) | m] := by
    apply condExp_congr_ae
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]
  _ =ᵐ[μ] fun ω => B (hf.mk f ω) (μ[g | m] ω) := by
    refine condExp_stronglyMeasurable_bilin_of_bound B hm hf.stronglyMeasurable_mk
      hg c ?_
    filter_upwards [hf_bound, hf.ae_eq_mk] with ω hω1 hω2
    rwa [← hω2]
  _ =ᵐ[μ] fun ω => B (f ω) (μ[g | m] ω) := by
    filter_upwards [hf.ae_eq_mk] with ω hω using by rw [hω]

中文:
定理 condExp_aestronglyMeasurable_bilin_of_bound
  结论: [完备空间 E]
  证明: calc
  μ[fun ω => B (f ω) (g ω) | m]
  _ =ᵐ[μ] μ[fun ω => B (hf.mk f ω) (g ω) | m] := by
    apply condExp_congr_ae
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]
  _ =ᵐ[μ] fun ω => B (hf.mk f ω) (μ[g | m] ω) := by
    refine condExp_stronglyMeasurable_bilin_of_bound B hm hf.stronglyMeasurable_mk
      hg c ?_
    filter_upwards [hf_bound, hf.ae_eq_mk] with ω hω1 hω2
    rwa [← hω2]
  _ =ᵐ[μ] fun ω => B (f ω) (μ[g | m] ω) := by
    filter_upwards [hf.ae_eq_mk] with ω hω using by rw [hω]
-/
theorem condExp_aestronglyMeasurable_bilin_of_bound [CompleteSpace E]
    (hm : m <= mΩ) [IsFiniteMeasure μ] {f : Ω -> F} {g : Ω -> E} (hf : AEStronglyMeasurable[m] f μ)
    (hg : Integrable g μ) (c : Real) (hf_bound : forallᵐ ω ∂μ, ‖f ω‖ <= c) :
    μ[fun ω => B (f ω) (g ω) | m] =ᵐ[μ] fun ω => B (f ω) (μ[g | m] ω) := calc
  μ[fun ω => B (f ω) (g ω) | m]
  _ =ᵐ[μ] μ[fun ω => B (hf.mk f ω) (g ω) | m] := by
    apply condExp_congr_ae
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]
  _ =ᵐ[μ] fun ω => B (hf.mk f ω) (μ[g | m] ω) := by
    refine condExp_stronglyMeasurable_bilin_of_bound B hm hf.stronglyMeasurable_mk
      hg c ?_
    filter_upwards [hf_bound, hf.ae_eq_mk] with ω hω1 hω2
    rwa [← hω2]
  _ =ᵐ[μ] fun ω => B (f ω) (μ[g | m] ω) := by
    filter_upwards [hf.ae_eq_mk] with ω hω using by rw [hω]

/--
theorem `condExp_bilin_of_stronglyMeasurable_left` / 定理 `condExp_bilin_of_stronglyMeasurable_left`

English:
theorem condExp_bilin_of_stronglyMeasurable_left
  statement: [CompleteSpace E] {f : Ω -> F} {g : Ω -> E}
  proof: by
by_cases hm : m <= mΩ; swap; · exact ae_of_all _ by simp [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
swap; · exact ae_of_all _ by simp [condExp_of_not_sigmaFinite hm hμm]
  obtain ⟨sets, sets_prop, h_univ⟩ := hf.exists_spanning_measurableSet_norm_le hm μ
  simp_rw [forall_and] at sets_prop
  obtain ⟨h_meas, h_finite, h_norm⟩ := sets_prop
  suffices forall n, forallᵐ ω ∂μ, ω in sets n -> (μ[fun ω => B (f ω) (g ω) | m]) ω = B (f ω) (μ[g | m] ω) by
    rw [← ae_all_iff] at this
    filter_upwards [this] with ω hω
    obtain ⟨i, hi⟩ : exists i, ω in sets i := by
      have h_mem : ω in ⋃ i, sets i := by rw [h_univ]; exact Set.mem_univ _
      simpa using h_mem
    exact hω i hi
  refine fun n => ae_imp_of_ae_restrict ?_
  suffices (μ.restrict (sets n))[fun ω => B (f ω) (g ω) | m] =ᵐ[μ.restrict (sets n)]
      fun ω => B (f ω) ((μ.restrict (sets n))[g | m] ω) by
    refine (condExp_restrict_ae_eq_restrict hm (h_meas n) hfg).symm.trans ?_
    filter_upwards [this, (condExp_restrict_ae_eq_restrict hm (h_meas n) hg)] with ω hω1 hω2
    rw [hω1]; rw [hω2]
  suffices (μ.restrict (sets n))[fun ω => B ((sets n).indicator f ω) (g ω) | m]
      =ᵐ[μ.restrict (sets n)] fun ω => B ((sets n).indicator f ω) ((μ.restrict (sets n))[g | m] ω) by
    refine EventuallyEq.trans (condExp_congr_ae ?_) (this.trans ?_)
    · filter_upwards [indicator_ae_eq_restrict (f := f) <| hm _ <| h_meas n] with ω hω
      rw [hω]
    · filter_upwards [indicator_ae_eq_restrict (f := f) <| hm _ <| h_meas n] with ω hω
      rw [hω]
  have : IsFiniteMeasure (μ.restrict (sets n)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact h_finite n
  refine condExp_stronglyMeasurable_bilin_of_bound B hm (hf.indicator (h_meas n))
    hg.integrableOn n ?_
  filter_upwards with ω
  by_cases hωs : ω in sets n <;> simp [hωs, h_norm]

中文:
定理 condExp_bilin_of_stronglyMeasurable_left
  结论: [完备空间 E] {f : Ω -> F} {g : Ω -> E}
  证明: by
by_cases hm : m <= mΩ; swap; · exact ae_of_all _ by simp [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
swap; · exact ae_of_all _ by simp [condExp_of_not_sigmaFinite hm hμm]
  obtain ⟨sets, sets_prop, h_univ⟩ := hf.exists_spanning_measurableSet_norm_le hm μ
  simp_rw [forall_and] at sets_prop
  obtain ⟨h_meas, h_finite, h_norm⟩ := sets_prop
  suffices forall n, forallᵐ ω ∂μ, ω in sets n -> (μ[fun ω => B (f ω) (g ω) | m]) ω = B (f ω) (μ[g | m] ω) by
    rw [← ae_all_iff] at this
    filter_upwards [this] with ω hω
    obtain ⟨i, hi⟩ : exists i, ω in sets i := by
      have h_mem : ω in ⋃ i, sets i := by rw [h_univ]; exact Set.mem_univ _
      simpa using h_mem
    exact hω i hi
  refine fun n => ae_imp_of_ae_restrict ?_
  suffices (μ.restrict (sets n))[fun ω => B (f ω) (g ω) | m] =ᵐ[μ.restrict (sets n)]
      fun ω => B (f ω) ((μ.restrict (sets n))[g | m] ω) by
    refine (condExp_restrict_ae_eq_restrict hm (h_meas n) hfg).symm.trans ?_
    filter_upwards [this, (condExp_restrict_ae_eq_restrict hm (h_meas n) hg)] with ω hω1 hω2
    rw [hω1]; rw [hω2]
  suffices (μ.restrict (sets n))[fun ω => B ((sets n).indicator f ω) (g ω) | m]
      =ᵐ[μ.restrict (sets n)] fun ω => B ((sets n).indicator f ω) ((μ.restrict (sets n))[g | m] ω) by
    refine EventuallyEq.trans (condExp_congr_ae ?_) (this.trans ?_)
    · filter_upwards [indicator_ae_eq_restrict (f := f) <| hm _ <| h_meas n] with ω hω
      rw [hω]
    · filter_upwards [indicator_ae_eq_restrict (f := f) <| hm _ <| h_meas n] with ω hω
      rw [hω]
  have : IsFiniteMeasure (μ.restrict (sets n)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact h_finite n
  refine condExp_stronglyMeasurable_bilin_of_bound B hm (hf.indicator (h_meas n))
    hg.integrableOn n ?_
  filter_upwards with ω
  by_cases hωs : ω in sets n <;> simp [hωs, h_norm]

Depends on / 依赖: SigmaFinite, ae_all_iff, ae_of_all, condExp_of_not_le, condExp_of_not_sigmaFinite, exists_spanning_measurableSet_norm_le, filter_upwa, forall_and, h_finite, h_meas, h_norm, h_univ, hf.exists_spanning_measurableSet_norm_le, sets_prop, simp_rw
-/
theorem condExp_bilin_of_stronglyMeasurable_left [CompleteSpace E] {f : Ω -> F} {g : Ω -> E}
    (hf : StronglyMeasurable[m] f) (hfg : Integrable (fun ω => B (f ω) (g ω)) μ)
    (hg : Integrable g μ) :
    μ[fun ω => B (f ω) (g ω) | m] =ᵐ[μ] fun ω => B (f ω) (μ[g | m] ω) := by
by_cases hm : m <= mΩ; swap; · exact ae_of_all _ by simp [condExp_of_not_le hm]
  by_cases hμm : SigmaFinite (μ.trim hm)
swap; · exact ae_of_all _ by simp [condExp_of_not_sigmaFinite hm hμm]
  obtain ⟨sets, sets_prop, h_univ⟩ := hf.exists_spanning_measurableSet_norm_le hm μ
  simp_rw [forall_and] at sets_prop
  obtain ⟨h_meas, h_finite, h_norm⟩ := sets_prop
  suffices forall n, forallᵐ ω ∂μ, ω in sets n -> (μ[fun ω => B (f ω) (g ω) | m]) ω = B (f ω) (μ[g | m] ω) by
    rw [← ae_all_iff] at this
    filter_upwards [this] with ω hω
    obtain ⟨i, hi⟩ : exists i, ω in sets i := by
      have h_mem : ω in ⋃ i, sets i := by rw [h_univ]; exact Set.mem_univ _
      simpa using h_mem
    exact hω i hi
  refine fun n => ae_imp_of_ae_restrict ?_
  suffices (μ.restrict (sets n))[fun ω => B (f ω) (g ω) | m] =ᵐ[μ.restrict (sets n)]
      fun ω => B (f ω) ((μ.restrict (sets n))[g | m] ω) by
    refine (condExp_restrict_ae_eq_restrict hm (h_meas n) hfg).symm.trans ?_
    filter_upwards [this, (condExp_restrict_ae_eq_restrict hm (h_meas n) hg)] with ω hω1 hω2
    rw [hω1]; rw [hω2]
  suffices (μ.restrict (sets n))[fun ω => B ((sets n).indicator f ω) (g ω) | m]
      =ᵐ[μ.restrict (sets n)] fun ω => B ((sets n).indicator f ω) ((μ.restrict (sets n))[g | m] ω) by
    refine EventuallyEq.trans (condExp_congr_ae ?_) (this.trans ?_)
    · filter_upwards [indicator_ae_eq_restrict (f := f) <| hm _ <| h_meas n] with ω hω
      rw [hω]
    · filter_upwards [indicator_ae_eq_restrict (f := f) <| hm _ <| h_meas n] with ω hω
      rw [hω]
  have : IsFiniteMeasure (μ.restrict (sets n)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact h_finite n
  refine condExp_stronglyMeasurable_bilin_of_bound B hm (hf.indicator (h_meas n))
    hg.integrableOn n ?_
  filter_upwards with ω
  by_cases hωs : ω in sets n <;> simp [hωs, h_norm]

/--
theorem `condExp_bilin_of_stronglyMeasurable_right` / 定理 `condExp_bilin_of_stronglyMeasurable_right`

English:
theorem condExp_bilin_of_stronglyMeasurable_right
  statement: [CompleteSpace F] {f : Ω -> F} {g : Ω -> E}
  proof: by
  simp_rw [← B.flip_apply] at hfg ⊢
  exact condExp_bilin_of_stronglyMeasurable_left B.flip hg hfg hf

中文:
定理 condExp_bilin_of_stronglyMeasurable_right
  结论: [完备空间 F] {f : Ω -> F} {g : Ω -> E}
  证明: by
  simp_rw [← B.flip_apply] at hfg ⊢
  exact condExp_bilin_of_stronglyMeasurable_left B.flip hg hfg hf

Depends on / 依赖: B.flip, B.flip_apply, condExp_bilin_of_stronglyMeasurable_left, flip_apply, simp_rw
-/
theorem condExp_bilin_of_stronglyMeasurable_right [CompleteSpace F] {f : Ω -> F} {g : Ω -> E}
    (hg : StronglyMeasurable[m] g)
    (hfg : Integrable (fun ω => B (f ω) (g ω)) μ) (hf : Integrable f μ) :
    μ[fun ω => B (f ω) (g ω) | m] =ᵐ[μ] fun ω => B (μ[f | m] ω) (g ω) := by
  simp_rw [← B.flip_apply] at hfg ⊢
  exact condExp_bilin_of_stronglyMeasurable_left B.flip hg hfg hf

/--
theorem `condExp_bilin_of_aestronglyMeasurable_left` / 定理 `condExp_bilin_of_aestronglyMeasurable_left`

English:
theorem condExp_bilin_of_aestronglyMeasurable_left
  statement: [CompleteSpace E]
  proof: calc
  μ[fun ω => B (f ω) (g ω) | m]
  _ =ᵐ[μ] μ[fun ω => B (hf.mk f ω) (g ω) | m] := by
    apply condExp_congr_ae
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]
  _ =ᵐ[μ] fun ω => B (hf.mk f ω) (μ[g | m] ω) := by
    refine condExp_bilin_of_stronglyMeasurable_left B hf.stronglyMeasurable_mk
      ((integrable_congr ?_).mp hfg) hg
    filter_upwards [hf.ae_eq_mk] with ω hω using by rw [hω]
  _ =ᵐ[μ] fun ω => B (f ω) (μ[g | m] ω) := by
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]

中文:
定理 condExp_bilin_of_aestronglyMeasurable_left
  结论: [完备空间 E]
  证明: calc
  μ[fun ω => B (f ω) (g ω) | m]
  _ =ᵐ[μ] μ[fun ω => B (hf.mk f ω) (g ω) | m] := by
    apply condExp_congr_ae
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]
  _ =ᵐ[μ] fun ω => B (hf.mk f ω) (μ[g | m] ω) := by
    refine condExp_bilin_of_stronglyMeasurable_left B hf.stronglyMeasurable_mk
      ((integrable_congr ?_).mp hfg) hg
    filter_upwards [hf.ae_eq_mk] with ω hω using by rw [hω]
  _ =ᵐ[μ] fun ω => B (f ω) (μ[g | m] ω) := by
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]
-/
theorem condExp_bilin_of_aestronglyMeasurable_left [CompleteSpace E]
    {f : Ω -> F} {g : Ω -> E} (hf : AEStronglyMeasurable[m] f μ)
    (hfg : Integrable (fun ω => B (f ω) (g ω)) μ) (hg : Integrable g μ) :
    μ[fun ω => B (f ω) (g ω) | m] =ᵐ[μ] fun ω => B (f ω) (μ[g | m] ω) := calc
  μ[fun ω => B (f ω) (g ω) | m]
  _ =ᵐ[μ] μ[fun ω => B (hf.mk f ω) (g ω) | m] := by
    apply condExp_congr_ae
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]
  _ =ᵐ[μ] fun ω => B (hf.mk f ω) (μ[g | m] ω) := by
    refine condExp_bilin_of_stronglyMeasurable_left B hf.stronglyMeasurable_mk
      ((integrable_congr ?_).mp hfg) hg
    filter_upwards [hf.ae_eq_mk] with ω hω using by rw [hω]
  _ =ᵐ[μ] fun ω => B (f ω) (μ[g | m] ω) := by
    filter_upwards [hf.ae_eq_mk] with a ha using by rw [ha]

/--
theorem `condExp_bilin_of_aestronglyMeasurable_right` / 定理 `condExp_bilin_of_aestronglyMeasurable_right`

English:
theorem condExp_bilin_of_aestronglyMeasurable_right
  statement: [CompleteSpace F] {f : Ω -> F} {g : Ω -> E}
  proof: by
  simp_rw [← B.flip_apply] at hfg ⊢
  exact condExp_bilin_of_aestronglyMeasurable_left B.flip hg hfg hf

中文:
定理 condExp_bilin_of_aestronglyMeasurable_right
  结论: [完备空间 F] {f : Ω -> F} {g : Ω -> E}
  证明: by
  simp_rw [← B.flip_apply] at hfg ⊢
  exact condExp_bilin_of_aestronglyMeasurable_left B.flip hg hfg hf

Depends on / 依赖: B.flip, B.flip_apply, condExp_bilin_of_aestronglyMeasurable_left, flip_apply, simp_rw
-/
theorem condExp_bilin_of_aestronglyMeasurable_right [CompleteSpace F] {f : Ω -> F} {g : Ω -> E}
    (hg : AEStronglyMeasurable[m] g μ)
    (hfg : Integrable (fun ω => B (f ω) (g ω)) μ) (hf : Integrable f μ) :
    μ[fun ω => B (f ω) (g ω) | m] =ᵐ[μ] fun ω => B (μ[f | m] ω) (g ω) := by
  simp_rw [← B.flip_apply] at hfg ⊢
  exact condExp_bilin_of_aestronglyMeasurable_left B.flip hg hfg hf

/--
theorem `condExp_smul_of_aestronglyMeasurable_left` / 定理 `condExp_smul_of_aestronglyMeasurable_left`

English:
theorem condExp_smul_of_aestronglyMeasurable_left
  statement: [CompleteSpace E] {f : Ω -> Real} {g : Ω -> E}
  proof: condExp_bilin_of_aestronglyMeasurable_left (.lsmul Real Real) hf hfg hg

中文:
定理 condExp_smul_of_aestronglyMeasurable_left
  结论: [完备空间 E] {f : Ω -> 实数} {g : Ω -> E}
  证明: condExp_bilin_of_aestronglyMeasurable_left (.lsmul Real Real) hf hfg hg

Depends on / 依赖: condExp_bilin_of_aestronglyMeasurable_left
-/
theorem condExp_smul_of_aestronglyMeasurable_left [CompleteSpace E] {f : Ω -> Real} {g : Ω -> E}
    (hf : AEStronglyMeasurable[m] f μ) (hfg : Integrable (f • g) μ) (hg : Integrable g μ) :
    μ[f • g | m] =ᵐ[μ] f • μ[g | m] :=
  condExp_bilin_of_aestronglyMeasurable_left (.lsmul Real Real) hf hfg hg

/--
theorem `condExp_smul_of_aestronglyMeasurable_right` / 定理 `condExp_smul_of_aestronglyMeasurable_right`

English:
theorem condExp_smul_of_aestronglyMeasurable_right
  statement: [CompleteSpace E] {f : Ω -> Real} {g : Ω -> E}
  proof: condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.lsmul Real Real).flip hg hfg hf

中文:
定理 condExp_smul_of_aestronglyMeasurable_right
  结论: [完备空间 E] {f : Ω -> 实数} {g : Ω -> E}
  证明: condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.lsmul Real Real).flip hg hfg hf

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.lsmul, condExp_bilin_of_aestronglyMeasurable_left
-/
theorem condExp_smul_of_aestronglyMeasurable_right [CompleteSpace E] {f : Ω -> Real} {g : Ω -> E}
    (hf : Integrable f μ) (hfg : Integrable (f • g) μ) (hg : AEStronglyMeasurable[m] g μ) :
    μ[f • g | m] =ᵐ[μ] μ[f | m] • g :=
  condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.lsmul Real Real).flip hg hfg hf

/--
theorem `condExp_mul_of_aestronglyMeasurable_left` / 定理 `condExp_mul_of_aestronglyMeasurable_left`

English:
theorem condExp_mul_of_aestronglyMeasurable_left
  statement: {f g : Ω -> Real} (hf : AEStronglyMeasurable[m] f μ)
  proof: condExp_bilin_of_aestronglyMeasurable_left (.mul Real Real) hf hfg hg

中文:
定理 condExp_mul_of_aestronglyMeasurable_left
  结论: {f g : Ω -> 实数} (hf : AEStronglyMeasurable[m] f μ)
  证明: condExp_bilin_of_aestronglyMeasurable_left (.mul Real Real) hf hfg hg

Depends on / 依赖: condExp_bilin_of_aestronglyMeasurable_left
-/
theorem condExp_mul_of_aestronglyMeasurable_left {f g : Ω -> Real} (hf : AEStronglyMeasurable[m] f μ)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) : μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
  condExp_bilin_of_aestronglyMeasurable_left (.mul Real Real) hf hfg hg

/--
theorem `condExp_mul_of_aestronglyMeasurable_right` / 定理 `condExp_mul_of_aestronglyMeasurable_right`

English:
theorem condExp_mul_of_aestronglyMeasurable_right
  statement: {f g : Ω -> Real} (hg : AEStronglyMeasurable[m] g μ)
  proof: condExp_bilin_of_aestronglyMeasurable_right (.mul Real Real) hg hfg hf

中文:
定理 condExp_mul_of_aestronglyMeasurable_right
  结论: {f g : Ω -> 实数} (hg : AEStronglyMeasurable[m] g μ)
  证明: condExp_bilin_of_aestronglyMeasurable_right (.mul Real Real) hg hfg hf

Depends on / 依赖: condExp_bilin_of_aestronglyMeasurable_right
-/
theorem condExp_mul_of_aestronglyMeasurable_right {f g : Ω -> Real} (hg : AEStronglyMeasurable[m] g μ)
    (hfg : Integrable (f * g) μ) (hf : Integrable f μ) : μ[f * g | m] =ᵐ[μ] μ[f | m] * g :=
  condExp_bilin_of_aestronglyMeasurable_right (.mul Real Real) hg hfg hf

/--
theorem `condExp_mul_of_stronglyMeasurable_left` / 定理 `condExp_mul_of_stronglyMeasurable_left`

English:
theorem condExp_mul_of_stronglyMeasurable_left
  statement: {f g : Ω -> Real} (hf : StronglyMeasurable[m] f)
  proof: condExp_bilin_of_aestronglyMeasurable_left (.mul Real Real)
    hf.aestronglyMeasurable hfg hg

中文:
定理 condExp_mul_of_stronglyMeasurable_left
  结论: {f g : Ω -> 实数} (hf : StronglyMeasurable[m] f)
  证明: condExp_bilin_of_aestronglyMeasurable_left (.mul Real Real)
    hf.aestronglyMeasurable hfg hg

Depends on / 依赖: aestronglyMeasurable, condExp_bilin_of_aestronglyMeasurable_left, hf.aestronglyMeasurable
-/
theorem condExp_mul_of_stronglyMeasurable_left {f g : Ω -> Real} (hf : StronglyMeasurable[m] f)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) : μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
  condExp_bilin_of_aestronglyMeasurable_left (.mul Real Real)
    hf.aestronglyMeasurable hfg hg

/--
lemma `condExp_mul_of_stronglyMeasurable_right` / 引理 `condExp_mul_of_stronglyMeasurable_right`

English:
lemma condExp_mul_of_stronglyMeasurable_right
  statement: {f g : Ω -> Real} (hg : StronglyMeasurable[m] g)
  proof: condExp_bilin_of_aestronglyMeasurable_right (.mul Real Real)
    hg.aestronglyMeasurable hfg hf

中文:
引理 condExp_mul_of_stronglyMeasurable_right
  结论: {f g : Ω -> 实数} (hg : StronglyMeasurable[m] g)
  证明: condExp_bilin_of_aestronglyMeasurable_right (.mul Real Real)
    hg.aestronglyMeasurable hfg hf

Depends on / 依赖: aestronglyMeasurable, condExp_bilin_of_aestronglyMeasurable_right, hg.aestronglyMeasurable
-/
lemma condExp_mul_of_stronglyMeasurable_right {f g : Ω -> Real} (hg : StronglyMeasurable[m] g)
    (hfg : Integrable (f * g) μ) (hf : Integrable f μ) : μ[f * g | m] =ᵐ[μ] μ[f | m] * g :=
  condExp_bilin_of_aestronglyMeasurable_right (.mul Real Real)
    hg.aestronglyMeasurable hfg hf

/--
theorem `condExp_stronglyMeasurable_simpleFunc_mul` / 定理 `condExp_stronglyMeasurable_simpleFunc_mul`

English:
theorem condExp_stronglyMeasurable_simpleFunc_mul
  statement: (hm : m <= mΩ) (f : @SimpleFunc Ω m Real) {g : Ω -> Real}
  proof: condExp_stronglyMeasurable_simpleFunc_bilin (.mul Real Real) hm f hg

中文:
定理 condExp_stronglyMeasurable_simpleFunc_mul
  结论: (hm : m <= mΩ) (f : @SimpleFunc Ω m 实数) {g : Ω -> 实数}
  证明: condExp_stronglyMeasurable_simpleFunc_bilin (.mul Real Real) hm f hg

Depends on / 依赖: condExp_stronglyMeasurable_simpleFunc_bilin
-/
theorem condExp_stronglyMeasurable_simpleFunc_mul (hm : m <= mΩ) (f : @SimpleFunc Ω m Real) {g : Ω -> Real}
    (hg : Integrable g μ) : μ[(f * g : Ω -> Real) | m] =ᵐ[μ] f * μ[g | m] :=
  condExp_stronglyMeasurable_simpleFunc_bilin (.mul Real Real) hm f hg

/--
theorem `condExp_stronglyMeasurable_mul_of_bound` / 定理 `condExp_stronglyMeasurable_mul_of_bound`

English:
theorem condExp_stronglyMeasurable_mul_of_bound
  statement: (hm : m <= mΩ) [IsFiniteMeasure μ] {f g : Ω -> Real}
  proof: condExp_stronglyMeasurable_bilin_of_bound (.mul Real Real) hm hf hg c hf_bound

中文:
定理 condExp_stronglyMeasurable_mul_of_bound
  结论: (hm : m <= mΩ) [是有限测度 μ] {f g : Ω -> 实数}
  证明: condExp_stronglyMeasurable_bilin_of_bound (.mul Real Real) hm hf hg c hf_bound

Depends on / 依赖: condExp_stronglyMeasurable_bilin_of_bound, hf_bound
-/
theorem condExp_stronglyMeasurable_mul_of_bound (hm : m <= mΩ) [IsFiniteMeasure μ] {f g : Ω -> Real}
    (hf : StronglyMeasurable[m] f) (hg : Integrable g μ) (c : Real) (hf_bound : forallᵐ ω ∂μ, ‖f ω‖ <= c) :
    μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
  condExp_stronglyMeasurable_bilin_of_bound (.mul Real Real) hm hf hg c hf_bound

/--
theorem `condExp_stronglyMeasurable_mul_of_bound₀` / 定理 `condExp_stronglyMeasurable_mul_of_bound₀`

English:
theorem condExp_stronglyMeasurable_mul_of_bound₀
  statement: (hm : m <= mΩ) [IsFiniteMeasure μ] {f g : Ω -> Real}
  proof: condExp_aestronglyMeasurable_bilin_of_bound (.mul Real Real) hm hf hg c hf_bound

中文:
定理 condExp_stronglyMeasurable_mul_of_bound₀
  结论: (hm : m <= mΩ) [是有限测度 μ] {f g : Ω -> 实数}
  证明: condExp_aestronglyMeasurable_bilin_of_bound (.mul Real Real) hm hf hg c hf_bound

Depends on / 依赖: condExp_aestronglyMeasurable_bilin_of_bound, hf_bound
-/
theorem condExp_stronglyMeasurable_mul_of_bound₀ (hm : m <= mΩ) [IsFiniteMeasure μ] {f g : Ω -> Real}
    (hf : AEStronglyMeasurable[m] f μ) (hg : Integrable g μ) (c : Real)
    (hf_bound : forallᵐ ω ∂μ, ‖f ω‖ <= c) : μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
  condExp_aestronglyMeasurable_bilin_of_bound (.mul Real Real) hm hf hg c hf_bound

end MeasureTheory
