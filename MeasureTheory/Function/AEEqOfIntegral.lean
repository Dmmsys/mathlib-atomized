/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Order.Filter.Ring

/-! # From equality of integrals to equality of functions

This file provides various statements of the general form "if two functions have the same integral
on all sets, then they are equal almost everywhere".
The different lemmas use various hypotheses on the class of functions, on the target space or on the
possible finiteness of the measure.

This file is about Bochner integrals. See the file `AEEqOfLIntegral` for Lebesgue integrals.

## Main statements

All results listed below apply to two functions `f, g`, together with two main hypotheses,
* `f` and `g` are integrable on all measurable sets with finite measure,
* for all measurable sets `s` with finite measure, `∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ`.

The conclusion is then `f =ᵐ[μ] g`. The main lemmas are:
* `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`: case of a sigma-finite measure.
* `AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq`: for functions which are
  `AEFinStronglyMeasurable`.
* `Lp.ae_eq_of_forall_setIntegral_eq`: for elements of `Lp`, for `0 < p < ∞`.
* `Integrable.ae_eq_of_forall_setIntegral_eq`: for integrable functions.

For each of these results, we also provide a lemma about the equality of one function and 0. For
example, `Lp.ae_eq_zero_of_forall_setIntegral_eq_zero`.

Generally useful lemmas which are not related to integrals:
* `ae_eq_zero_of_forall_inner`: if for all constants `c`, `(fun x => ⟪c, f x⟫_𝕜) =ᵐ[μ] 0` then
  `f =ᵐ[μ] 0`.
* `ae_eq_zero_of_forall_dual`: if for all constants `c` in the `StrongDual` space,
  `fun x => c (f x) =ᵐ[μ] 0` then `f =ᵐ[μ] 0`.

-/

public section


open MeasureTheory TopologicalSpace NormedSpace Filter

open scoped ENNReal NNReal MeasureTheory Topology

namespace MeasureTheory

section AeEqOfForall

variable {α E 𝕜 : Type*} {m : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]

open scoped InnerProductSpace in
/--
theorem `ae_eq_zero_of_forall_inner` / 定理 `ae_eq_zero_of_forall_inner`

English:
theorem ae_eq_zero_of_forall_inner
  statement: [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  proof: by
  let s := denseSeq E
  have hs : DenseRange s := denseRange_denseSeq E
  have hf' : forallᵐ x ∂μ, forall n : Nat, ⟪s n, f x⟫_𝕜 = 0 := ae_all_iff.mpr fun n => hf (s n)
  refine hf'.mono fun x hx => ?_
  rw [Pi.zero_apply]; rw [← @inner_self_eq_zero 𝕜]
  have h_closed : IsClosed {c : E | ⟪c, f x⟫_

中文:
定理 ae_eq_zero_of_对任意_inner
  结论: [赋范交换加群 E] [内积空间 𝕜 E]
  证明: by
  let s := denseSeq E
  have hs : DenseRange s := denseRange_denseSeq E
  have hf' : forallᵐ x ∂μ, forall n : Nat, ⟪s n, f x⟫_𝕜 = 0 := ae_all_iff.mpr fun n => hf (s n)
  refine hf'.mono fun x hx => ?_
  rw [Pi.zero_apply]; rw [← @inner_self_eq_zero 𝕜]
  have h_closed : IsClosed {c : E | ⟪c, f x⟫_

Depends on / 依赖: DenseRange, IsClosed, Pi.zero_apply, ae_all_iff, ae_all_iff.mpr, denseRange_denseSeq, denseSeq, fun_prop, h_closed, inner_self_eq_zero, isClosed_eq, isClosed_property, zero_apply
-/
theorem ae_eq_zero_of_forall_inner [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [SecondCountableTopology E] {f : α -> E} (hf : forall c : E, (fun x => ⟪c, f x⟫_𝕜) =ᵐ[μ] 0) :
    f =ᵐ[μ] 0 := by
  let s := denseSeq E
  have hs : DenseRange s := denseRange_denseSeq E
  have hf' : forallᵐ x ∂μ, forall n : Nat, ⟪s n, f x⟫_𝕜 = 0 := ae_all_iff.mpr fun n => hf (s n)
  refine hf'.mono fun x hx => ?_
  rw [Pi.zero_apply]; rw [← @inner_self_eq_zero 𝕜]
  have h_closed : IsClosed {c : E | ⟪c, f x⟫_𝕜 = 0} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  exact @isClosed_property Nat E _ s (fun c => ⟪c, f x⟫_𝕜 = 0) hs h_closed hx _

local notation "⟪" x ", " y "⟫" => y x

variable (𝕜)

/--
theorem `ae_eq_zero_of_forall_dual_of_isSeparable` / 定理 `ae_eq_zero_of_forall_dual_of_isSeparable`

English:
theorem ae_eq_zero_of_forall_dual_of_isSeparable
  statement: [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  proof: by
  rcases ht with ⟨d, d_count, hd⟩
  have : Encodable d := d_count.toEncodable
  have : forall x : d, exists g : StrongDual 𝕜 E, ‖g‖ <= 1 ∧ g x = ‖(x : E)‖ :=
    fun x => exists_dual_vector'' 𝕜 (x : E)
  choose s hs using this
  have A : forall a : E, a in t -> (forall x, ⟪a, s x⟫ = (0 : 𝕜)) -> a

中文:
定理 ae_eq_zero_of_对任意_dual_of_isSeparable
  结论: [赋范交换加群 E] [赋范空间 𝕜 E]
  证明: by
  rcases ht with ⟨d, d_count, hd⟩
  have : Encodable d := d_count.toEncodable
  have : forall x : d, exists g : StrongDual 𝕜 E, ‖g‖ <= 1 ∧ g x = ‖(x : E)‖ :=
    fun x => exists_dual_vector'' 𝕜 (x : E)
  choose s hs using this
  have A : forall a : E, a in t -> (forall x, ⟪a, s x⟫ = (0 : 𝕜)) -> a

Depends on / 依赖: Encodable, StrongDual, a_mem, a_pos, closure, contrapose, d_count, d_count.toEncodable, exists_dual_vector, norm_pos_iff, not_false_iff, toEncodable
-/
theorem ae_eq_zero_of_forall_dual_of_isSeparable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {t : Set E} (ht : TopologicalSpace.IsSeparable t) {f : α -> E}
    (hf : forall c : StrongDual 𝕜 E, (fun x => ⟪f x, c⟫) =ᵐ[μ] 0) (h't : forallᵐ x ∂μ, f x in t) :
    f =ᵐ[μ] 0 := by
  rcases ht with ⟨d, d_count, hd⟩
  have : Encodable d := d_count.toEncodable
  have : forall x : d, exists g : StrongDual 𝕜 E, ‖g‖ <= 1 ∧ g x = ‖(x : E)‖ :=
    fun x => exists_dual_vector'' 𝕜 (x : E)
  choose s hs using this
  have A : forall a : E, a in t -> (forall x, ⟪a, s x⟫ = (0 : 𝕜)) -> a = 0 := by
    intro a hat ha
    contrapose! ha
    have a_pos : 0 < ‖a‖ := by simp only [ha, norm_pos_iff, Ne, not_false_iff]
    have a_mem : a in closure d := hd hat
    obtain ⟨x, hx⟩ : exists x : d, dist a x < ‖a‖ / 2 := by
      rcases Metric.mem_closure_iff.1 a_mem (‖a‖ / 2) (half_pos a_pos) with ⟨x, h'x, hx⟩
      exact ⟨⟨x, h'x⟩, hx⟩
    use x
    have I : ‖a‖ / 2 < ‖(x : E)‖ := by
      have : ‖a‖ <= ‖(x : E)‖ + ‖a - x‖ := norm_le_insert' _ _
      have : ‖a - x‖ < ‖a‖ / 2 := by rwa [dist_eq_norm] at hx
      linarith
    intro h
    apply lt_irrefl ‖s x x‖
    calc
      ‖s x x‖ = ‖s x (x - a)‖ := by simp only [h, sub_zero, map_sub]
      _ <= 1 * ‖(x : E) - a‖ := ContinuousLinearMap.le_of_opNorm_le _ (hs x).1 _
      _ < ‖a‖ / 2 := by rw [one_mul]; rwa [dist_eq_norm'] at hx
      _ < ‖(x : E)‖ := I
      _ = ‖s x x‖ := by simp [(hs x).2]
  have hfs : forall y : d, forallᵐ x ∂μ, ⟪f x, s y⟫ = (0 : 𝕜) := fun y => hf (s y)
  have hf' : forallᵐ x ∂μ, forall y : d, ⟪f x, s y⟫ = (0 : 𝕜) := by rwa [ae_all_iff]
  filter_upwards [hf', h't] with x hx h'x
  exact A (f x) h'x hx

/--
theorem `ae_eq_zero_of_forall_dual` / 定理 `ae_eq_zero_of_forall_dual`

English:
theorem ae_eq_zero_of_forall_dual
  statement: [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  proof: ae_eq_zero_of_forall_dual_of_isSeparable 𝕜 (.of_separableSpace Set.univ) hf
    (Eventually.of_forall fun _ => Set.mem_univ _)

中文:
定理 ae_eq_zero_of_对任意_dual
  结论: [赋范交换加群 E] [赋范空间 𝕜 E]
  证明: ae_eq_zero_of_forall_dual_of_isSeparable 𝕜 (.of_separableSpace Set.univ) hf
    (Eventually.of_forall fun _ => Set.mem_univ _)

Depends on / 依赖: Eventually, Eventually.of_forall, Set.mem_univ, Set.univ, ae_eq_zero_of_forall_dual_of_isSeparable, mem_univ, of_forall, of_separableSpace
-/
theorem ae_eq_zero_of_forall_dual [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SecondCountableTopology E] {f : α -> E}
    (hf : forall c : StrongDual 𝕜 E, (fun x => ⟪f x, c⟫) =ᵐ[μ] 0) : f =ᵐ[μ] 0 :=
  ae_eq_zero_of_forall_dual_of_isSeparable 𝕜 (.of_separableSpace Set.univ) hf
    (Eventually.of_forall fun _ => Set.mem_univ _)

end AeEqOfForall

variable {α E : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E] {p : Real>=0∞}

section AeEqOfForallSetIntegralEq

section Real

variable {f : α -> Real}

/--
theorem `ae_nonneg_of_forall_setIntegral_nonneg` / 定理 `ae_nonneg_of_forall_setIntegral_nonneg`

English:
theorem ae_nonneg_of_forall_setIntegral_nonneg
  statement: (hf : Integrable f μ)
  proof: by
  simp_rw [EventuallyLE, Pi.zero_apply]
  rw [ae_const_le_iff_forall_lt_measure_zero]
  intro b hb_neg
  let s := {x | f x <= b}
  have hs : NullMeasurableSet s μ := nullMeasurableSet_le hf.1.aemeasurable aemeasurable_const
  have mus : μ s < ∞ := Integrable.measure_le_lt_top hf hb_neg
  have h_i

中文:
定理 ae_nonneg_of_对任意_set整数egral_nonneg
  结论: (hf : 可积 f μ)
  证明: by
  simp_rw [EventuallyLE, Pi.zero_apply]
  rw [ae_const_le_iff_forall_lt_measure_zero]
  intro b hb_neg
  let s := {x | f x <= b}
  have hs : NullMeasurableSet s μ := nullMeasurableSet_le hf.1.aemeasurable aemeasurable_const
  have mus : μ s < ∞ := Integrable.measure_le_lt_top hf hb_neg
  have h_i

Depends on / 依赖: EventuallyLE, Integrable, Integrable.measure_le_lt_top, NullMeasurableSet, Pi.zero_apply, ae_const_le_iff_forall_lt_measure_zero, aemeasurable, aemeasurable_const, h_const_le, h_int_gt, hb_neg, hf.integrableOn, integrableOn, integrableOn_const, measure_le_lt_top, mus.ne, nullMeasurableSet_le, setIntegral_mono_ae_restrict, simp_rw, zero_apply
-/
theorem ae_nonneg_of_forall_setIntegral_nonneg (hf : Integrable f μ)
    (hf_zero : forall s, MeasurableSet s -> μ s < ∞ -> 0 <= ∫ x in s, f x ∂μ) : 0 <=ᵐ[μ] f := by
  simp_rw [EventuallyLE, Pi.zero_apply]
  rw [ae_const_le_iff_forall_lt_measure_zero]
  intro b hb_neg
  let s := {x | f x <= b}
  have hs : NullMeasurableSet s μ := nullMeasurableSet_le hf.1.aemeasurable aemeasurable_const
  have mus : μ s < ∞ := Integrable.measure_le_lt_top hf hb_neg
  have h_int_gt : (∫ x in s, f x ∂μ) <= b * μ.real s := by
    have h_const_le : (∫ x in s, f x ∂μ) <= ∫ _ in s, b ∂μ := by
      refine setIntegral_mono_ae_restrict hf.integrableOn (integrableOn_const mus.ne) ?_
      rw [EventuallyLE]; rw [ae_restrict_iff₀ (hs.mono μ.restrict_le_self)]
      exact Eventually.of_forall fun x hxs => hxs
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at h_const_le
  contrapose! h_int_gt with H
  calc
b * μ.real s < 0 := mul_neg_of_neg_of_pos hb_neg ENNReal.toReal_pos H mus.ne
    _ <= ∫ x in s, f x ∂μ := by
      rw [← μ.restrict_toMeasurable mus.ne]
      exact hf_zero _ (measurableSet_toMeasurable ..) (by rwa [measure_toMeasurable])

/--
theorem `ae_le_of_forall_setIntegral_le` / 定理 `ae_le_of_forall_setIntegral_le`

English:
theorem ae_le_of_forall_setIntegral_le
  statement: {f g : α -> Real} (hf : Integrable f μ) (hg : Integrable g μ)
  proof: by
  rw [← eventually_sub_nonneg]
  refine ae_nonneg_of_forall_setIntegral_nonneg (hg.sub hf) fun s hs => ?_
  rw [integral_sub' hg.integrableOn hf.integrableOn]; rw [sub_nonneg]
  exact hf_le s hs

中文:
定理 ae_le_of_对任意_set整数egral_le
  结论: {f g : α -> 实数} (hf : 可积 f μ) (hg : 可积 g μ)
  证明: by
  rw [← eventually_sub_nonneg]
  refine ae_nonneg_of_forall_setIntegral_nonneg (hg.sub hf) fun s hs => ?_
  rw [integral_sub' hg.integrableOn hf.integrableOn]; rw [sub_nonneg]
  exact hf_le s hs

Depends on / 依赖: ae_nonneg_of_forall_setIntegral_nonneg, eventually_sub_nonneg, hf.integrableOn, hf_le, hg.integrableOn, hg.sub, integrableOn, integral_sub, sub_nonneg
-/
theorem ae_le_of_forall_setIntegral_le {f g : α -> Real} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf_le : forall s, MeasurableSet s -> μ s < ∞ -> (∫ x in s, f x ∂μ) <= ∫ x in s, g x ∂μ) :
    f <=ᵐ[μ] g := by
  rw [← eventually_sub_nonneg]
  refine ae_nonneg_of_forall_setIntegral_nonneg (hg.sub hf) fun s hs => ?_
  rw [integral_sub' hg.integrableOn hf.integrableOn]; rw [sub_nonneg]
  exact hf_le s hs

/--
theorem `ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter` / 定理 `ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter`

English:
theorem ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
  statement: {f : α -> Real} {t : Set α}
  proof: by
  refine ae_nonneg_of_forall_setIntegral_nonneg hf fun s hs h's => ?_
  simp_rw [Measure.restrict_restrict hs]
  apply hf_zero s hs
  rwa [Measure.restrict_apply hs] at h's

中文:
定理 ae_nonneg_restrict_of_对任意_set整数egral_nonneg_inter
  结论: {f : α -> 实数} {t : 集合 α}
  证明: by
  refine ae_nonneg_of_forall_setIntegral_nonneg hf fun s hs h's => ?_
  simp_rw [Measure.restrict_restrict hs]
  apply hf_zero s hs
  rwa [Measure.restrict_apply hs] at h's

Depends on / 依赖: Measure, Measure.restrict_apply, Measure.restrict_restrict, ae_nonneg_of_forall_setIntegral_nonneg, hf_zero, restrict_apply, restrict_restrict, simp_rw
-/
theorem ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter {f : α -> Real} {t : Set α}
    (hf : IntegrableOn f t μ)
    (hf_zero : forall s, MeasurableSet s -> μ (s inter t) < ∞ -> 0 <= ∫ x in s inter t, f x ∂μ) :
    0 <=ᵐ[μ.restrict t] f := by
  refine ae_nonneg_of_forall_setIntegral_nonneg hf fun s hs h's => ?_
  simp_rw [Measure.restrict_restrict hs]
  apply hf_zero s hs
  rwa [Measure.restrict_apply hs] at h's

/--
theorem `ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite` / 定理 `ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite`

English:
theorem ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
  statement: [SigmaFinite μ] {f : α -> Real}
  proof: by
  apply ae_of_forall_measure_lt_top_ae_restrict
  intro t t_meas t_lt_top
  apply ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter (hf_int_finite t t_meas t_lt_top)
  intro s s_meas _
  exact
    hf_zero _ (s_meas.inter t_meas)
      (lt_of_le_of_lt (measure_mono (Set.inter_subset_right)) t_

中文:
定理 ae_nonneg_of_对任意_set整数egral_nonneg_of_sigmaFinite
  结论: [σ有限 μ] {f : α -> 实数}
  证明: by
  apply ae_of_forall_measure_lt_top_ae_restrict
  intro t t_meas t_lt_top
  apply ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter (hf_int_finite t t_meas t_lt_top)
  intro s s_meas _
  exact
    hf_zero _ (s_meas.inter t_meas)
      (lt_of_le_of_lt (measure_mono (Set.inter_subset_right)) t_

Depends on / 依赖: Set.inter_subset_right, ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter, ae_of_forall_measure_lt_top_ae_restrict, hf_int_finite, hf_zero, inter_subset_right, lt_of_le_of_lt, measure_mono, s_meas, s_meas.inter, t_lt_top, t_meas
-/
theorem ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite [SigmaFinite μ] {f : α -> Real}
    (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ)
    (hf_zero : forall s, MeasurableSet s -> μ s < ∞ -> 0 <= ∫ x in s, f x ∂μ) : 0 <=ᵐ[μ] f := by
  apply ae_of_forall_measure_lt_top_ae_restrict
  intro t t_meas t_lt_top
  apply ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter (hf_int_finite t t_meas t_lt_top)
  intro s s_meas _
  exact
    hf_zero _ (s_meas.inter t_meas)
      (lt_of_le_of_lt (measure_mono (Set.inter_subset_right)) t_lt_top)

/--
theorem `AEFinStronglyMeasurable.ae_nonneg_of_forall_setIntegral_nonneg` / 定理 `AEFinStronglyMeasurable.ae_nonneg_of_forall_setIntegral_nonneg`

English:
theorem AEFinStronglyMeasurable.ae_nonneg_of_forall_setIntegral_nonneg
  statement: {f : α -> Real}
  proof: by
  let t := hf.sigmaFiniteSet
  suffices 0 <=ᵐ[μ.restrict t] f from
    ae_of_ae_restrict_of_ae_restrict_compl _ this hf.ae_eq_zero_compl.symm.le
  have : SigmaFinite (μ.restrict t) := hf.sigmaFinite_restrict
  refine
    ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite (fun s hs hμts => ?_) 

中文:
定理 AEFinStronglyMeasurable.ae_nonneg_of_对任意_set整数egral_nonneg
  结论: {f : α -> 实数}
  证明: by
  let t := hf.sigmaFiniteSet
  suffices 0 <=ᵐ[μ.restrict t] f from
    ae_of_ae_restrict_of_ae_restrict_compl _ this hf.ae_eq_zero_compl.symm.le
  have : SigmaFinite (μ.restrict t) := hf.sigmaFinite_restrict
  refine
    ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite (fun s hs hμts => ?_) 

Depends on / 依赖: IntegrableOn, Measure, Measure.restrict_apply, Measure.restrict_restrict, SigmaFinite, ae_eq_zero_compl, ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite, ae_of_ae_restrict_of_ae_restrict_compl, hf.ae_eq_zero_compl.symm.le, hf.measurableSet, hf.sigmaFiniteSet, hf.sigmaFinite_restrict, hf_int_finite, hs.inter, measurableSet, restrict, restrict_apply, restrict_restrict, sigmaFiniteSet, sigmaFinite_restrict
-/
theorem AEFinStronglyMeasurable.ae_nonneg_of_forall_setIntegral_nonneg {f : α -> Real}
    (hf : AEFinStronglyMeasurable f μ)
    (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ)
    (hf_zero : forall s, MeasurableSet s -> μ s < ∞ -> 0 <= ∫ x in s, f x ∂μ) : 0 <=ᵐ[μ] f := by
  let t := hf.sigmaFiniteSet
  suffices 0 <=ᵐ[μ.restrict t] f from
    ae_of_ae_restrict_of_ae_restrict_compl _ this hf.ae_eq_zero_compl.symm.le
  have : SigmaFinite (μ.restrict t) := hf.sigmaFinite_restrict
  refine
    ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite (fun s hs hμts => ?_) fun s hs hμts => ?_
  · rw [IntegrableOn, Measure.restrict_restrict hs]
    rw [Measure.restrict_apply hs] at hμts
    exact hf_int_finite (s inter t) (hs.inter hf.measurableSet) hμts
  · rw [Measure.restrict_restrict hs]
    rw [Measure.restrict_apply hs] at hμts
    exact hf_zero (s inter t) (hs.inter hf.measurableSet) hμts

/--
theorem `ae_nonneg_restrict_of_forall_setIntegral_nonneg` / 定理 `ae_nonneg_restrict_of_forall_setIntegral_nonneg`

English:
theorem ae_nonneg_restrict_of_forall_setIntegral_nonneg
  statement: {f : α -> Real}
  proof: by
  refine
    ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
      (hf_int_finite t ht (lt_top_iff_ne_top.mpr hμt)) fun s hs _ => ?_
  refine hf_zero (s inter t) (hs.inter ht) ?_
  exact (measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμt)

中文:
定理 ae_nonneg_restrict_of_对任意_set整数egral_nonneg
  结论: {f : α -> 实数}
  证明: by
  refine
    ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
      (hf_int_finite t ht (lt_top_iff_ne_top.mpr hμt)) fun s hs _ => ?_
  refine hf_zero (s inter t) (hs.inter ht) ?_
  exact (measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμt)

Depends on / 依赖: Set.inter_subset_right, ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter, hf_int_finite, hf_zero, hs.inter, inter_subset_right, lt_top_iff_ne_top, lt_top_iff_ne_top.mpr, measure_mono, trans_lt
-/
theorem ae_nonneg_restrict_of_forall_setIntegral_nonneg {f : α -> Real}
    (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ)
    (hf_zero : forall s, MeasurableSet s -> μ s < ∞ -> 0 <= ∫ x in s, f x ∂μ) {t : Set α}
    (ht : MeasurableSet t) (hμt : μ t != ∞) : 0 <=ᵐ[μ.restrict t] f := by
  refine
    ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
      (hf_int_finite t ht (lt_top_iff_ne_top.mpr hμt)) fun s hs _ => ?_
  refine hf_zero (s inter t) (hs.inter ht) ?_
  exact (measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμt)

/--
theorem `ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real` / 定理 `ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real`

English:
theorem ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real
  statement: {f : α -> Real}
  proof: by
  suffices h_and : f <=ᵐ[μ.restrict t] 0 ∧ 0 <=ᵐ[μ.restrict t] f from
    h_and.1.mp (h_and.2.mono fun x hx1 hx2 => le_antisymm hx2 hx1)
  refine
    ⟨?_,
      ae_nonneg_restrict_of_forall_setIntegral_nonneg hf_int_finite
        (fun s hs hμs => (hf_zero s hs hμs).symm.le) ht hμt⟩
  suffices h_

中文:
定理 ae_eq_zero_restrict_of_对任意_set整数egral_eq_zero_real
  结论: {f : α -> 实数}
  证明: by
  suffices h_and : f <=ᵐ[μ.restrict t] 0 ∧ 0 <=ᵐ[μ.restrict t] f from
    h_and.1.mp (h_and.2.mono fun x hx1 hx2 => le_antisymm hx2 hx1)
  refine
    ⟨?_,
      ae_nonneg_restrict_of_forall_setIntegral_nonneg hf_int_finite
        (fun s hs hμs => (hf_zero s hs hμs).symm.le) ht hμt⟩
  suffices h_

Depends on / 依赖: Pi.neg_apply, ae_nonneg_restrict_of_forall_setIntegral_nonneg, h_and, h_neg, h_neg.mono, hf_int_finite, hf_zero, le_antisymm, neg_apply, restrict, symm.le
-/
theorem ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real {f : α -> Real}
    (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ)
    (hf_zero : forall s, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = 0) {t : Set α}
    (ht : MeasurableSet t) (hμt : μ t != ∞) : f =ᵐ[μ.restrict t] 0 := by
  suffices h_and : f <=ᵐ[μ.restrict t] 0 ∧ 0 <=ᵐ[μ.restrict t] f from
    h_and.1.mp (h_and.2.mono fun x hx1 hx2 => le_antisymm hx2 hx1)
  refine
    ⟨?_,
      ae_nonneg_restrict_of_forall_setIntegral_nonneg hf_int_finite
        (fun s hs hμs => (hf_zero s hs hμs).symm.le) ht hμt⟩
  suffices h_neg : 0 <=ᵐ[μ.restrict t] -f by
    refine h_neg.mono fun x hx => ?_
    rw [Pi.neg_apply] at hx
    simpa using hx
  refine
    ae_nonneg_restrict_of_forall_setIntegral_nonneg (fun s hs hμs => (hf_int_finite s hs hμs).neg)
      (fun s hs hμs => ?_) ht hμt
  simp_rw [Pi.neg_apply]
  rw [integral_neg]; rw [neg_nonneg]
  exact (hf_zero s hs hμs).le

end Real

/--
theorem `ae_eq_zero_restrict_of_forall_setIntegral_eq_zero` / 定理 `ae_eq_zero_restrict_of_forall_setIntegral_eq_zero`

English:
theorem ae_eq_zero_restrict_of_forall_setIntegral_eq_zero
  statement: {f : α -> E}
  proof: by
  rcases (hf_int_finite t ht hμt.lt_top).aestronglyMeasurable.isSeparable_ae_range with
    ⟨u, u_sep, hu⟩
  refine ae_eq_zero_of_forall_dual_of_isSeparable Real u_sep (fun c => ?_) hu
  refine ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real ?_ ?_ ht hμt
  · intro s hs hμs
    exact Contin

中文:
定理 ae_eq_zero_restrict_of_对任意_set整数egral_eq_zero
  结论: {f : α -> E}
  证明: by
  rcases (hf_int_finite t ht hμt.lt_top).aestronglyMeasurable.isSeparable_ae_range with
    ⟨u, u_sep, hu⟩
  refine ae_eq_zero_of_forall_dual_of_isSeparable Real u_sep (fun c => ?_) hu
  refine ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real ?_ ?_ ht hμt
  · intro s hs hμs
    exact Contin

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integrable_comp, ContinuousLinearMap.integral_comp_comm, ae_eq_zero_of_forall_dual_of_isSeparable, ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real, aestronglyMeasurable, aestronglyMeasurable.isSeparable_ae_range, hf_int_finite, hf_zero, integrable_comp, integral_comp_comm, isSeparable_ae_range, lt_top, map_zero, t.lt_top, u_sep
-/
theorem ae_eq_zero_restrict_of_forall_setIntegral_eq_zero {f : α -> E}
    (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ)
    (hf_zero : forall s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = 0) {t : Set α}
    (ht : MeasurableSet t) (hμt : μ t != ∞) : f =ᵐ[μ.restrict t] 0 := by
  rcases (hf_int_finite t ht hμt.lt_top).aestronglyMeasurable.isSeparable_ae_range with
    ⟨u, u_sep, hu⟩
  refine ae_eq_zero_of_forall_dual_of_isSeparable Real u_sep (fun c => ?_) hu
  refine ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real ?_ ?_ ht hμt
  · intro s hs hμs
    exact ContinuousLinearMap.integrable_comp c (hf_int_finite s hs hμs)
  · intro s hs hμs
    rw [ContinuousLinearMap.integral_comp_comm c (hf_int_finite s hs hμs)]; rw [hf_zero s hs hμs]
    exact map_zero _

/--
theorem `ae_eq_restrict_of_forall_setIntegral_eq` / 定理 `ae_eq_restrict_of_forall_setIntegral_eq`

English:
theorem ae_eq_restrict_of_forall_setIntegral_eq
  statement: {f g : α -> E}
  proof: by
  rw [← sub_ae_eq_zero]
  have hfg' : forall s : Set α, MeasurableSet s -> μ s < ∞ -> (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
    exact sub_eq_zero.mpr (hfg_zero s hs hμs)
  have hfg_int : forall s, MeasurableS

中文:
定理 ae_eq_restrict_of_对任意_set整数egral_eq
  结论: {f g : α -> E}
  证明: by
  rw [← sub_ae_eq_zero]
  have hfg' : forall s : Set α, MeasurableSet s -> μ s < ∞ -> (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
    exact sub_eq_zero.mpr (hfg_zero s hs hμs)
  have hfg_int : forall s, MeasurableS

Depends on / 依赖: IntegrableOn, MeasurableSet, ae_eq_zero_restrict_of_forall_setIntegral_eq_zero, hf_int_finite, hfg_int, hfg_zero, hg_int_finite, integral_sub, sub_ae_eq_zero, sub_eq_zero, sub_eq_zero.mpr
-/
theorem ae_eq_restrict_of_forall_setIntegral_eq {f g : α -> E}
    (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ)
    (hg_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn g s μ)
    (hfg_zero : forall s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    {t : Set α} (ht : MeasurableSet t) (hμt : μ t != ∞) : f =ᵐ[μ.restrict t] g := by
  rw [← sub_ae_eq_zero]
  have hfg' : forall s : Set α, MeasurableSet s -> μ s < ∞ -> (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
    exact sub_eq_zero.mpr (hfg_zero s hs hμs)
  have hfg_int : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn (f - g) s μ := fun s hs hμs =>
    (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact ae_eq_zero_restrict_of_forall_setIntegral_eq_zero hfg_int hfg' ht hμt

/--
theorem `ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite` / 定理 `ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite`

English:
theorem ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
  statement: [SigmaFinite μ] {f : α -> E}
  proof: by
  let S := spanningSets μ
  rw [← @Measure.restrict_univ _ _ μ]; rw [← iUnion_spanningSets μ]; rw [EventuallyEq]; rw [ae_iff]; rw [Measure.restrict_apply' (MeasurableSet.iUnion (measurableSet_spanningSets μ))]
  rw [Set.inter_iUnion]; rw [measure_iUnion_null_iff]
  intro n
  have h_meas_n : Measu

中文:
定理 ae_eq_zero_of_对任意_set整数egral_eq_of_sigmaFinite
  结论: [σ有限 μ] {f : α -> E}
  证明: by
  let S := spanningSets μ
  rw [← @Measure.restrict_univ _ _ μ]; rw [← iUnion_spanningSets μ]; rw [EventuallyEq]; rw [ae_iff]; rw [Measure.restrict_apply' (MeasurableSet.iUnion (measurableSet_spanningSets μ))]
  rw [Set.inter_iUnion]; rw [measure_iUnion_null_iff]
  intro n
  have h_meas_n : Measu

Depends on / 依赖: EventuallyEq, MeasurableSet, MeasurableSet.iUnion, Measure, Measure.restrict_apply, Measure.restrict_univ, Set.inter_iUnion, ae_eq_zero_restrict_of_forall_setIntegral_eq_zero, ae_iff, h_meas_n, hf_int_, iUnion, iUnion_spanningSets, inter_iUnion, measurableSet_spanningSets, measure_iUnion_null_iff, measure_spanningSets_lt_top, restrict_apply, restrict_univ, spanningSets
-/
theorem ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f : α -> E}
    (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ)
    (hf_zero : forall s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  let S := spanningSets μ
  rw [← @Measure.restrict_univ _ _ μ]; rw [← iUnion_spanningSets μ]; rw [EventuallyEq]; rw [ae_iff]; rw [Measure.restrict_apply' (MeasurableSet.iUnion (measurableSet_spanningSets μ))]
  rw [Set.inter_iUnion]; rw [measure_iUnion_null_iff]
  intro n
  have h_meas_n : MeasurableSet (S n) := measurableSet_spanningSets μ n
  have hμn : μ (S n) < ∞ := measure_spanningSets_lt_top μ n
  rw [← Measure.restrict_apply' h_meas_n]
  exact ae_eq_zero_restrict_of_forall_setIntegral_eq_zero hf_int_finite hf_zero h_meas_n hμn.ne

/--
theorem `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite` / 定理 `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`

English:
theorem ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  statement: [SigmaFinite μ] {f g : α -> E}
  proof: by
  rw [← sub_ae_eq_zero]
  have hfg : forall s : Set α, MeasurableSet s -> μ s < ∞ -> (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]; rw [sub_eq_zero.mpr (hfg_eq s hs hμs)]
  have hfg_int : forall s, MeasurableSet s ->

中文:
定理 ae_eq_of_对任意_set整数egral_eq_of_sigmaFinite
  结论: [σ有限 μ] {f g : α -> E}
  证明: by
  rw [← sub_ae_eq_zero]
  have hfg : forall s : Set α, MeasurableSet s -> μ s < ∞ -> (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]; rw [sub_eq_zero.mpr (hfg_eq s hs hμs)]
  have hfg_int : forall s, MeasurableSet s ->

Depends on / 依赖: IntegrableOn, MeasurableSet, ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite, hf_int_finite, hfg_eq, hfg_int, hg_int_finite, integral_sub, sub_ae_eq_zero, sub_eq_zero, sub_eq_zero.mpr
-/
theorem ae_eq_of_forall_setIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α -> E}
    (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ)
    (hg_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn g s μ)
    (hfg_eq : forall s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
    f =ᵐ[μ] g := by
  rw [← sub_ae_eq_zero]
  have hfg : forall s : Set α, MeasurableSet s -> μ s < ∞ -> (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]; rw [sub_eq_zero.mpr (hfg_eq s hs hμs)]
  have hfg_int : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn (f - g) s μ := fun s hs hμs =>
    (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite hfg_int hfg

/--
theorem `AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero` / 定理 `AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero`

English:
theorem AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero
  statement: {f : α -> E}
  proof: by
  let t := hf.sigmaFiniteSet
  suffices f =ᵐ[μ.restrict t] 0 from
    ae_of_ae_restrict_of_ae_restrict_compl _ this hf.ae_eq_zero_compl
  have : SigmaFinite (μ.restrict t) := hf.sigmaFinite_restrict
  refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_
  · intro s hs hμs
    rw [Integ

中文:
定理 AEFinStronglyMeasurable.ae_eq_zero_of_对任意_set整数egral_eq_zero
  结论: {f : α -> E}
  证明: by
  let t := hf.sigmaFiniteSet
  suffices f =ᵐ[μ.restrict t] 0 from
    ae_of_ae_restrict_of_ae_restrict_compl _ this hf.ae_eq_zero_compl
  have : SigmaFinite (μ.restrict t) := hf.sigmaFinite_restrict
  refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_
  · intro s hs hμs
    rw [Integ

Depends on / 依赖: IntegrableOn, Measure, Measure.restrict_apply, Measure.restrict_restrict, SigmaFinite, ae_eq_zero_compl, ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite, ae_of_ae_restrict_of_ae_restrict_compl, hf.ae_eq_zero_compl, hf.measurableSet, hf.sigmaFiniteSet, hf.sigmaFinite_restrict, hf_int_finite, hs.inter, measurableSet, restrict, restrict_apply, restrict_restrict, sigmaFiniteSet, sigmaFinite_restrict
-/
theorem AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero {f : α -> E}
    (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ)
    (hf_zero : forall s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = 0)
    (hf : AEFinStronglyMeasurable f μ) : f =ᵐ[μ] 0 := by
  let t := hf.sigmaFiniteSet
  suffices f =ᵐ[μ.restrict t] 0 from
    ae_of_ae_restrict_of_ae_restrict_compl _ this hf.ae_eq_zero_compl
  have : SigmaFinite (μ.restrict t) := hf.sigmaFinite_restrict
  refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_
  · intro s hs hμs
    rw [IntegrableOn]; rw [Measure.restrict_restrict hs]
    rw [Measure.restrict_apply hs] at hμs
    exact hf_int_finite _ (hs.inter hf.measurableSet) hμs
  · intro s hs hμs
    rw [Measure.restrict_restrict hs]
    rw [Measure.restrict_apply hs] at hμs
    exact hf_zero _ (hs.inter hf.measurableSet) hμs

/--
theorem `AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq` / 定理 `AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq`

English:
theorem AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq
  statement: {f g : α -> E}
  proof: by
  rw [← sub_ae_eq_zero]
  have hfg : forall s : Set α, MeasurableSet s -> μ s < ∞ -> (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]; rw [sub_eq_zero.mpr (hfg_eq s hs hμs)]
  have hfg_int : forall s, MeasurableSet s ->

中文:
定理 AEFinStronglyMeasurable.ae_eq_of_对任意_set整数egral_eq
  结论: {f g : α -> E}
  证明: by
  rw [← sub_ae_eq_zero]
  have hfg : forall s : Set α, MeasurableSet s -> μ s < ∞ -> (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]; rw [sub_eq_zero.mpr (hfg_eq s hs hμs)]
  have hfg_int : forall s, MeasurableSet s ->

Depends on / 依赖: IntegrableOn, MeasurableSet, ae_eq_zero_of_forall_setIntegral_eq_zero, hf.sub, hf_int_finite, hfg_eq, hfg_int, hg_int_finite, integral_sub, sub_ae_eq_zero, sub_eq_zero, sub_eq_zero.mpr
-/
theorem AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq {f g : α -> E}
    (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ)
    (hg_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn g s μ)
    (hfg_eq : forall s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    (hf : AEFinStronglyMeasurable f μ) (hg : AEFinStronglyMeasurable g μ) : f =ᵐ[μ] g := by
  rw [← sub_ae_eq_zero]
  have hfg : forall s : Set α, MeasurableSet s -> μ s < ∞ -> (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]; rw [sub_eq_zero.mpr (hfg_eq s hs hμs)]
  have hfg_int : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn (f - g) s μ := fun s hs hμs =>
    (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact (hf.sub hg).ae_eq_zero_of_forall_setIntegral_eq_zero hfg_int hfg

/--
theorem `Lp.ae_eq_zero_of_forall_setIntegral_eq_zero` / 定理 `Lp.ae_eq_zero_of_forall_setIntegral_eq_zero`

English:
theorem Lp.ae_eq_zero_of_forall_setIntegral_eq_zero
  statement: (f : Lp E p μ) (hp_ne_zero : p != 0)
  proof: AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero hf_int_finite hf_zero
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable

中文:
定理 Lp.ae_eq_zero_of_对任意_set整数egral_eq_zero
  结论: (f : Lp E p μ) (hp_ne_zero : p != 0)
  证明: AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero hf_int_finite hf_zero
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable

Depends on / 依赖: AEFinStronglyMeasurable, AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero, Lp.finStronglyMeasurable, ae_eq_zero_of_forall_setIntegral_eq_zero, aefinStronglyMeasurable, finStronglyMeasurable, hf_int_finite, hf_zero, hp_ne_top, hp_ne_zero
-/
theorem Lp.ae_eq_zero_of_forall_setIntegral_eq_zero (f : Lp E p μ) (hp_ne_zero : p != 0)
    (hp_ne_top : p != ∞) (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ)
    (hf_zero : forall s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0 :=
  AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero hf_int_finite hf_zero
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable

/--
theorem `Lp.ae_eq_of_forall_setIntegral_eq` / 定理 `Lp.ae_eq_of_forall_setIntegral_eq`

English:
theorem Lp.ae_eq_of_forall_setIntegral_eq
  statement: (f g : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  proof: AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq hf_int_finite hg_int_finite hfg
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable

中文:
定理 Lp.ae_eq_of_对任意_set整数egral_eq
  结论: (f g : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
  证明: AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq hf_int_finite hg_int_finite hfg
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable

Depends on / 依赖: AEFinStronglyMeasurable, AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq, Lp.finStronglyMeasurable, ae_eq_of_forall_setIntegral_eq, aefinStronglyMeasurable, finStronglyMeasurable, hf_int_finite, hg_int_finite, hp_ne_top, hp_ne_zero
-/
theorem Lp.ae_eq_of_forall_setIntegral_eq (f g : Lp E p μ) (hp_ne_zero : p != 0) (hp_ne_top : p != ∞)
    (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ)
    (hg_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn g s μ)
    (hfg : forall s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
    f =ᵐ[μ] g :=
  AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq hf_int_finite hg_int_finite hfg
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable

/--
theorem `ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim` / 定理 `ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim`

English:
theorem ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim
  statement: (hm : m <= m0) {f : α -> E}
  proof: by
  obtain ⟨t, ht_meas, htf_zero, htμ⟩ := hf.exists_set_sigmaFinite
  have : SigmaFinite ((μ.restrict t).trim hm) := by rwa [restrict_trim hm μ ht_meas] at htμ
  have htf_zero : f =ᵐ[μ.restrict tᶜ] 0 := by
    rw [EventuallyEq]; rw [ae_restrict_iff' (MeasurableSet.compl (hm _ ht_meas))]
    exact E

中文:
定理 ae_eq_zero_of_对任意_set整数egral_eq_of_finStronglyMeasurable_trim
  结论: (hm : m <= m0) {f : α -> E}
  证明: by
  obtain ⟨t, ht_meas, htf_zero, htμ⟩ := hf.exists_set_sigmaFinite
  have : SigmaFinite ((μ.restrict t).trim hm) := by rwa [restrict_trim hm μ ht_meas] at htμ
  have htf_zero : f =ᵐ[μ.restrict tᶜ] 0 := by
    rw [EventuallyEq]; rw [ae_restrict_iff' (MeasurableSet.compl (hm _ ht_meas))]
    exact E

Depends on / 依赖: Eventually, Eventually.of_forall, EventuallyEq, MeasurableSet, MeasurableSet.compl, SigmaFinite, StronglyMeasurable, ae_of_ae_restrict_of_ae_restrict_compl, ae_restrict_iff, exists_set_sigmaFinite, hf.exists_set_sigmaFinite, hf.stronglyMeasurable, hf_meas_m, ht_meas, htf_zero, measure_eq_zero_of_tri, of_forall, restrict, restrict_trim, stronglyMeasurable
-/
theorem ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim (hm : m <= m0) {f : α -> E}
    (hf_int_finite : forall s, MeasurableSet[m] s -> μ s < ∞ -> IntegrableOn f s μ)
    (hf_zero : forall s : Set α, MeasurableSet[m] s -> μ s < ∞ -> ∫ x in s, f x ∂μ = 0)
    (hf : FinStronglyMeasurable f (μ.trim hm)) : f =ᵐ[μ] 0 := by
  obtain ⟨t, ht_meas, htf_zero, htμ⟩ := hf.exists_set_sigmaFinite
  have : SigmaFinite ((μ.restrict t).trim hm) := by rwa [restrict_trim hm μ ht_meas] at htμ
  have htf_zero : f =ᵐ[μ.restrict tᶜ] 0 := by
    rw [EventuallyEq]; rw [ae_restrict_iff' (MeasurableSet.compl (hm _ ht_meas))]
    exact Eventually.of_forall htf_zero
  have hf_meas_m : StronglyMeasurable[m] f := hf.stronglyMeasurable
  suffices f =ᵐ[μ.restrict t] 0 from
    ae_of_ae_restrict_of_ae_restrict_compl _ this htf_zero
  refine measure_eq_zero_of_trim_eq_zero hm ?_
  refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_
  · intro s hs hμs
    unfold IntegrableOn
    rw [restrict_trim hm (μ.restrict t) hs]; rw [Measure.restrict_restrict (hm s hs)]
    rw [← restrict_trim hm μ ht_meas]; rw [Measure.restrict_apply hs]; rw [trim_measurableSet_eq hm (hs.inter ht_meas)] at hμs
    refine Integrable.trim hm ?_ hf_meas_m
    exact hf_int_finite _ (hs.inter ht_meas) hμs
  · intro s hs hμs
    rw [restrict_trim hm (μ.restrict t) hs]; rw [Measure.restrict_restrict (hm s hs)]
    rw [← restrict_trim hm μ ht_meas]; rw [Measure.restrict_apply hs]; rw [trim_measurableSet_eq hm (hs.inter ht_meas)] at hμs
    rw [← integral_trim hm hf_meas_m]
    exact hf_zero _ (hs.inter ht_meas) hμs

/--
theorem `Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero` / 定理 `Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero`

English:
theorem Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero
  statement: {f : α -> E} (hf : Integrable f μ)
  proof: hf.aefinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero
    (fun _ _ _ => hf.integrableOn) hf_zero

中文:
定理 可积.ae_eq_zero_of_对任意_set整数egral_eq_zero
  结论: {f : α -> E} (hf : 可积 f μ)
  证明: hf.aefinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero
    (fun _ _ _ => hf.integrableOn) hf_zero

Depends on / 依赖: ae_eq_zero_of_forall_setIntegral_eq_zero, aefinStronglyMeasurable, hf.aefinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero, hf.integrableOn, hf_zero, integrableOn
-/
theorem Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero {f : α -> E} (hf : Integrable f μ)
    (hf_zero : forall s, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0 :=
  hf.aefinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero
    (fun _ _ _ => hf.integrableOn) hf_zero

/--
theorem `Integrable.ae_eq_of_forall_setIntegral_eq` / 定理 `Integrable.ae_eq_of_forall_setIntegral_eq`

English:
theorem Integrable.ae_eq_of_forall_setIntegral_eq
  statement: (f g : α -> E) (hf : Integrable f μ)
  proof: AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq (fun _ _ _ => hf.integrableOn)
    (fun _ _ _ => hg.integrableOn) hfg hf.aefinStronglyMeasurable hg.aefinStronglyMeasurable

中文:
定理 可积.ae_eq_of_对任意_set整数egral_eq
  结论: (f g : α -> E) (hf : 可积 f μ)
  证明: AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq (fun _ _ _ => hf.integrableOn)
    (fun _ _ _ => hg.integrableOn) hfg hf.aefinStronglyMeasurable hg.aefinStronglyMeasurable

Depends on / 依赖: AEFinStronglyMeasurable, AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq, ae_eq_of_forall_setIntegral_eq, aefinStronglyMeasurable, hf.aefinStronglyMeasurable, hf.integrableOn, hg.aefinStronglyMeasurable, hg.integrableOn, integrableOn
-/
theorem Integrable.ae_eq_of_forall_setIntegral_eq (f g : α -> E) (hf : Integrable f μ)
    (hg : Integrable g μ)
    (hfg : forall s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
    f =ᵐ[μ] g :=
  AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq (fun _ _ _ => hf.integrableOn)
    (fun _ _ _ => hg.integrableOn) hfg hf.aefinStronglyMeasurable hg.aefinStronglyMeasurable

variable {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]

/--
lemma `ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero` / 引理 `ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero`

English:
lemma ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero
  statement: {μ : Measure β} {f : β -> E}
  proof: by
  suffices forall s, MeasurableSet s -> ∫ x in s, f x ∂μ = 0 from
    hf.ae_eq_zero_of_forall_setIntegral_eq_zero (fun s hs _ => this s hs)
  have A : forall (t : Set β), MeasurableSet t -> ∫ (x : β) in t, f x ∂μ = 0
      -> ∫ (x : β) in tᶜ, f x ∂μ = 0 := by
    intro t t_meas ht
    have I : ∫ 

中文:
引理 ae_eq_zero_of_对任意_set整数egral_isClosed_eq_zero
  结论: {μ : 测度 β} {f : β -> E}
  证明: by
  suffices forall s, MeasurableSet s -> ∫ x in s, f x ∂μ = 0 from
    hf.ae_eq_zero_of_forall_setIntegral_eq_zero (fun s hs _ => this s hs)
  have A : forall (t : Set β), MeasurableSet t -> ∫ (x : β) in t, f x ∂μ = 0
      -> ∫ (x : β) in tᶜ, f x ∂μ = 0 := by
    intro t t_meas ht
    have I : ∫ 

Depends on / 依赖: MeasurableSet, MeasurableSet.induction_on_open, ae_eq_zero_of_forall_setIntegral_eq_zero, compl_com, hf.ae_eq_zero_of_forall_setIntegral_eq_zero, induction_on_open, integral_add_compl, isClosed_univ, isOpen, setIntegral_univ, t_meas
-/
lemma ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero {μ : Measure β} {f : β -> E}
    (hf : Integrable f μ) (h'f : forall (s : Set β), IsClosed s -> ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  suffices forall s, MeasurableSet s -> ∫ x in s, f x ∂μ = 0 from
    hf.ae_eq_zero_of_forall_setIntegral_eq_zero (fun s hs _ => this s hs)
  have A : forall (t : Set β), MeasurableSet t -> ∫ (x : β) in t, f x ∂μ = 0
      -> ∫ (x : β) in tᶜ, f x ∂μ = 0 := by
    intro t t_meas ht
    have I : ∫ x, f x ∂μ = 0 := by rw [← setIntegral_univ]; exact h'f _ isClosed_univ
    simpa [ht, I] using integral_add_compl t_meas hf
  intro s hs
  induction s, hs using MeasurableSet.induction_on_open with
  | isOpen U hU => exact compl_compl U ▸ A _ hU.measurableSet.compl (h'f _ hU.isClosed_compl)
  | compl s hs ihs => exact A s hs ihs
  | iUnion g g_disj g_meas hg => simp [integral_iUnion g_meas g_disj hf.integrableOn, hg]

/--
lemma `ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero` / 引理 `ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero`

English:
lemma ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero
  proof: by
  apply ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hf (fun s hs => ?_)
  let t : Nat -> Set β := fun n => closure (compactCovering β n) inter s
  suffices H : Tendsto (fun n => ∫ x in t n, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) by
    have A : forall n, ∫ x in t n, f x ∂μ = 0 :=
      fun n 

中文:
引理 ae_eq_zero_of_对任意_set整数egral_isCompact_eq_zero
  证明: by
  apply ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hf (fun s hs => ?_)
  let t : Nat -> Set β := fun n => closure (compactCovering β n) inter s
  suffices H : Tendsto (fun n => ∫ x in t n, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) by
    have A : forall n, ∫ x in t n, f x ∂μ = 0 :=
      fun n 

Depends on / 依赖: H.symm, Set.iUnion_inter, Tendsto, ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero, closure, closure.inter_right, compactCovering, iUnion_closure_compactCovering, iUnion_inter, inter_right, isCompact_compactCovering, simp_rw, tendsto_const_nhds_iff
-/
lemma ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero
    [SigmaCompactSpace β] [R1Space β] {μ : Measure β} {f : β -> E} (hf : Integrable f μ)
    (h'f : forall (s : Set β), IsCompact s -> ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  apply ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hf (fun s hs => ?_)
  let t : Nat -> Set β := fun n => closure (compactCovering β n) inter s
  suffices H : Tendsto (fun n => ∫ x in t n, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) by
    have A : forall n, ∫ x in t n, f x ∂μ = 0 :=
      fun n => h'f _ ((isCompact_compactCovering β n).closure.inter_right hs)
    simp_rw [A, tendsto_const_nhds_iff] at H
    exact H.symm
  have B : s = ⋃ n, t n := by
    rw [← Set.iUnion_inter]; rw [iUnion_closure_compactCovering]; rw [Set.univ_inter]
  rw [B]
  apply tendsto_setIntegral_of_monotone
  · intro n
    exact (isClosed_closure.inter hs).measurableSet
  · intro m n hmn
    simp only [t]
    gcongr
  · exact hf.integrableOn

/--
lemma `ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'` / 引理 `ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'`

English:
lemma ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
  proof: by
  rw [← μ.restrict_univ]; rw [← iUnion_closure_compactCovering]
  apply (ae_restrict_iUnion_iff _ _).2 (fun n => ?_)
  apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero
  · exact hf.integrableOn_isCompact (isCompact_compactCovering β n).closure
  · intro s hs
    rw [Measure.restrict_restr

中文:
引理 ae_eq_zero_of_对任意_set整数egral_isCompact_eq_zero'
  证明: by
  rw [← μ.restrict_univ]; rw [← iUnion_closure_compactCovering]
  apply (ae_restrict_iUnion_iff _ _).2 (fun n => ?_)
  apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero
  · exact hf.integrableOn_isCompact (isCompact_compactCovering β n).closure
  · intro s hs
    rw [Measure.restrict_restr

Depends on / 依赖: Measure, Measure.restrict_restrict, ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero, ae_restrict_iUnion_iff, closure, hf.integrableOn_isCompact, hs.inter_right, iUnion_closure_compactCovering, integrableOn_isCompact, inter_right, isClosed_closure, isCompact_compactCovering, measurableSet_closure, restrict_restrict, restrict_univ
-/
lemma ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
    [SigmaCompactSpace β] [R1Space β] {μ : Measure β} {f : β -> E} (hf : LocallyIntegrable f μ)
    (h'f : forall (s : Set β), IsCompact s -> ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  rw [← μ.restrict_univ]; rw [← iUnion_closure_compactCovering]
  apply (ae_restrict_iUnion_iff _ _).2 (fun n => ?_)
  apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero
  · exact hf.integrableOn_isCompact (isCompact_compactCovering β n).closure
  · intro s hs
    rw [Measure.restrict_restrict' measurableSet_closure]
    exact h'f _ (hs.inter_right isClosed_closure)

end AeEqOfForallSetIntegralEq

end MeasureTheory
