/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
public import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Class `IsDeterministic` of deterministic kernels

This file defines the class `IsDeterministic` of deterministic kernels, and proves some
properties about them.

## Main definitions

* `Kernel.IsDeterministic`: a kernel is deterministic if copying then applying the kernel to the
  two copies is the same as first applying the kernel then copying.

## Main statements

* `isDeterministic_iff_isZeroOneMeasure`: a finite kernel is deterministic if and
  only if it is a zero-one measure for every input.
* `IsDeterministic.exists_eq_deterministic`: in a standard Borel space, a deterministic Markov
  kernel is a Dirac kernel of some measurable function.
* `comp_parallelComp_comp_copy`: if the composition of two Markov kernels `η ∘ₖ κ` is
  deterministic, the distribution over both `η ∘ₖ κ` and `κ` can be obtained by computing `η ∘ₖ κ`
  and `κ` independently. This corresponds to the equation of a Positive Markov category.
  See Example 11.25 of [fritz2020].

## Implementation notes

`comp_parallelComp_comp_copy` is true only when considering Markov kernels. To see why, consider
the counterexample with $X = Y = \{\varnothing\}$, kernels $\kappa(\cdot | \varnothing) = 2\delta_
{\varnothing}$ and $\eta(\cdot | \varnothing) = (1/2)\delta_{\varnothing}$: although their
composition is deterministic, the equation fails.

## References

* [A synthetic approach to
  Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020]
* [Moss and Perrone, *A category-theoretic proof of the ergodic decomposition theorem*][moss2023]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace ProbabilityTheory

/--
Definition of `IsDeterministic` / `IsDeterministic` 的定义

English:
class IsDeterministic
  parameters: (κ : Kernel α β)
  axioms and operations (1):
    - parallelComp_self_comp_copy' : (κ ∥ₖ κ) ∘ₖ Kernel.copy α = Kernel.copy β ∘ₖ κ

中文:
类 是确定性
  参数: (κ : 核 α β)
  公理与运算 (1 个):
    - parallelComp_self_comp_copy' : (κ ∥ₖ κ) ∘ₖ 核.copy α = 核.copy β ∘ₖ κ
-/
class IsDeterministic (κ : Kernel α β) : Prop where
  parallelComp_self_comp_copy' : (κ ∥ₖ κ) ∘ₖ Kernel.copy α = Kernel.copy β ∘ₖ κ

namespace Kernel

/--
lemma `parallelComp_self_comp_copy` / 引理 `parallelComp_self_comp_copy`

English:
lemma parallelComp_self_comp_copy
  given: {κ : Kernel α β} [IsDeterministic κ]
  proof: IsDeterministic.parallelComp_self_comp_copy'

中文:
引理 parallelComp_self_comp_copy
  条件: {κ : 核 α β} [是确定性 κ]
  证明: IsDeterministic.parallelComp_self_comp_copy'

Depends on / 依赖: IsDeterministic, IsDeterministic.parallelComp_self_comp_copy, parallelComp_self_comp_copy
-/
lemma parallelComp_self_comp_copy {κ : Kernel α β} [IsDeterministic κ] :
    (κ ∥ₖ κ) ∘ₖ Kernel.copy α = Kernel.copy β ∘ₖ κ :=
  IsDeterministic.parallelComp_self_comp_copy'

instance {f : α -> β} (hf : Measurable f) : IsDeterministic (deterministic f hf) where
  parallelComp_self_comp_copy' := by
    simp_rw [parallelComp_comp_copy, deterministic_prod_deterministic, copy,
      deterministic_comp_deterministic, Function.comp_def, Function.diag_def]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDeterministic (mβ := mα) (Kernel.id (α := α))
  body: by unfold Kernel.id; infer_instance

中文:
实例 :
  签名: 是确定性 (mβ := mα) (核.id (α := α))
  定义体: by unfold Kernel.id; infer_instance

Depends on / 依赖: Kernel, Kernel.id, infer_instance, of_isLocalization
-/
instance : IsDeterministic (mβ := mα) (Kernel.id (α := α)) := by unfold Kernel.id; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDeterministic (copy α)
  body: by unfold copy; infer_instance

中文:
实例 :
  签名: 是确定性 (copy α)
  定义体: by unfold copy; infer_instance

Depends on / 依赖: IsFractionRing, QuasiFinite, infer_instance
-/
instance : IsDeterministic (copy α) := by unfold copy; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDeterministic (discard α)
  body: by unfold discard; infer_instance

中文:
实例 :
  签名: 是确定性 (discard α)
  定义体: by unfold discard; infer_instance

Depends on / 依赖: discard, infer_instance
-/
instance : IsDeterministic (discard α) := by unfold discard; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDeterministic (swap α β)
  body: by unfold swap; infer_instance

中文:
实例 :
  签名: 是确定性 (swap α β)
  定义体: by unfold swap; infer_instance

Depends on / 依赖: infer_instance
-/
instance : IsDeterministic (swap α β) := by unfold swap; infer_instance

open IsZeroOneMeasure

/--
lemma `isDeterministic_iff_isZeroOneMeasure` / 引理 `isDeterministic_iff_isZeroOneMeasure`

English:
lemma isDeterministic_iff_isZeroOneMeasure
  given: (κ : Kernel α β) [IsFiniteKernel κ]
  proof: by
  constructor
  · intro h a
    refine ⟨fun s hs => ?_⟩
DFunLike.congr_fun have := DFunLike.congr_fun κ.parallelComp_self_comp_copy a
 (s ×ˢ s)
    rw [parallelComp_comp_copy]; rw [prod_apply_prod]; rw [copy_comp_apply_prod]; rw [inter_self] at this
    · by_cases hκ : κ a s = 0
      · simp [hκ]

中文:
引理 isDeterministic_iff_isZeroOneMeasure
  条件: (κ : 核 α β) [是FiniteKernel κ]
  证明: by
  constructor
  · intro h a
    refine ⟨fun s hs => ?_⟩
DFunLike.congr_fun have := DFunLike.congr_fun κ.parallelComp_self_comp_copy a
 (s ×ˢ s)
    rw [parallelComp_comp_copy]; rw [prod_apply_prod]; rw [copy_comp_apply_prod]; rw [inter_self] at this
    · by_cases hκ : κ a s = 0
      · simp [hκ]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, ENNReal, ENNReal.mul_eq_left, Measure, Measure.prod_eq, Or.inr, all_goals, congr_fun, copy_comp_apply_prod, inter_self, mul_eq_left, parallelComp_comp_copy, parallelComp_self_comp_copy, prod_apply, prod_apply_prod, prod_eq
-/
lemma isDeterministic_iff_isZeroOneMeasure (κ : Kernel α β) [IsFiniteKernel κ] :
    IsDeterministic κ ↔ forall a, IsZeroOneMeasure (κ a) := by
  constructor
  · intro h a
    refine ⟨fun s hs => ?_⟩
DFunLike.congr_fun have := DFunLike.congr_fun κ.parallelComp_self_comp_copy a
 (s ×ˢ s)
    rw [parallelComp_comp_copy]; rw [prod_apply_prod]; rw [copy_comp_apply_prod]; rw [inter_self] at this
    · by_cases hκ : κ a s = 0
      · simp [hκ]
· exact Or.inr (ENNReal.mul_eq_left hκ (by simp)).mp this
    all_goals exact hs
  · intro _
    refine ⟨?_⟩
    ext : 1
    rw [parallelComp_comp_copy]; rw [prod_apply]
    refine Measure.prod_eq fun s t hs ht => ?_
    rw [copy_comp_apply_prod _ _ hs ht]
    exact measure_inter_eq_prod hs ht

instance (κ : Kernel α β) [IsFiniteKernel κ] [IsDeterministic κ] : forall a, IsZeroOneMeasure (κ a) :=
  (isDeterministic_iff_isZeroOneMeasure κ).mp ‹_›

/--
theorem `IsDeterministic.exists_eq_deterministic` / 定理 `IsDeterministic.exists_eq_deterministic`

English:
theorem IsDeterministic.exists_eq_deterministic
  statement: [StandardBorelSpace β] (κ : Kernel α β)
  proof: by
  choose f hf using fun a => exists_eq_dirac (μ := κ a)
  refine ⟨f, ?_, ?_⟩
  · intro s hs
    have : f ⁻¹' s = (fun a => κ a s) ⁻¹' {1} := by
      simp only [preimage, mem_singleton_iff]
      simp_rw [hf, Measure.dirac_apply' _ hs]
      ext x
      exact (indicator_eq_one_iff_mem ENNReal).sy

中文:
定理 是确定性.存在_eq_deterministic
  结论: [StandardBorel空间 β] (κ : 核 α β)
  证明: by
  choose f hf using fun a => exists_eq_dirac (μ := κ a)
  refine ⟨f, ?_, ?_⟩
  · intro s hs
    have : f ⁻¹' s = (fun a => κ a s) ⁻¹' {1} := by
      simp only [preimage, mem_singleton_iff]
      simp_rw [hf, Measure.dirac_apply' _ hs]
      ext x
      exact (indicator_eq_one_iff_mem ENNReal).sy

Depends on / 依赖: ENNReal, Measure, Measure.dirac_apply, dirac_apply, exists_eq_dirac, indicator_eq_one_iff_mem, measurableSet_singleton, measurable_coe, mem_singleton_iff, preimage, simp_rw
-/
theorem IsDeterministic.exists_eq_deterministic [StandardBorelSpace β] (κ : Kernel α β)
    [IsMarkovKernel κ] [IsDeterministic κ] :
    exists (f : α -> β) (hf : Measurable f), κ = deterministic f hf := by
  choose f hf using fun a => exists_eq_dirac (μ := κ a)
  refine ⟨f, ?_, ?_⟩
  · intro s hs
    have : f ⁻¹' s = (fun a => κ a s) ⁻¹' {1} := by
      simp only [preimage, mem_singleton_iff]
      simp_rw [hf, Measure.dirac_apply' _ hs]
      ext x
      exact (indicator_eq_one_iff_mem ENNReal).symm
    rw [this]
exact κ.measurable_coe hs measurableSet_singleton 1
  · ext a : 1
    exact hf a

/--
lemma `comp_parallelComp_comp_copy` / 引理 `comp_parallelComp_comp_copy`

English:
lemma comp_parallelComp_comp_copy
  statement: {γ : Type*} [MeasurableSpace γ] {κ : Kernel α β}
  proof: by
  simp only [parallelComp_comp_copy]
  ext a : 1
  rw [prod_apply]
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [comp_apply' _ _ _ (hs.prod ht)]
  simp_rw [prod_apply_prod, Kernel.id_apply, Measure.dirac_apply' _ ht]
  have (b : β) : (η b) s * t.indicator 1 b = t.indicator (fun b => η b s) b

中文:
引理 comp_parallelComp_comp_copy
  结论: {γ : 类型} [可测空间 γ] {κ : 核 α β}
  证明: by
  simp only [parallelComp_comp_copy]
  ext a : 1
  rw [prod_apply]
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [comp_apply' _ _ _ (hs.prod ht)]
  simp_rw [prod_apply_prod, Kernel.id_apply, Measure.dirac_apply' _ ht]
  have (b : β) : (η b) s * t.indicator 1 b = t.indicator (fun b => η b s) b

Depends on / 依赖: Kernel, Kernel.id_apply, Measure, Measure.dirac_apply, Measure.prod_eq, all_goals, comp_apply, dirac_apply, hs.prod, id_apply, indicator, lintegral_indicator, measurable_coe, parallelComp_comp_copy, prod_apply, prod_apply_prod, prod_eq, setLIntegral_eq_zero_iff, simp_rw, split_ifs
-/
lemma comp_parallelComp_comp_copy {γ : Type*} [MeasurableSpace γ] {κ : Kernel α β}
    {η : Kernel β γ} [IsMarkovKernel κ] [IsMarkovKernel η] [IsDeterministic (η ∘ₖ κ)] :
    η ∘ₖ κ ∥ₖ κ ∘ₖ copy α = η ∥ₖ Kernel.id ∘ₖ copy β ∘ₖ κ := by
  simp only [parallelComp_comp_copy]
  ext a : 1
  rw [prod_apply]
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [comp_apply' _ _ _ (hs.prod ht)]
  simp_rw [prod_apply_prod, Kernel.id_apply, Measure.dirac_apply' _ ht]
  have (b : β) : (η b) s * t.indicator 1 b = t.indicator (fun b => η b s) b := by
    simp only [indicator]
    split_ifs
    all_goals simp_all
  simp_rw [this]
  rw [lintegral_indicator ht]
  rcases ((η ∘ₖ κ) a).zero_one s with (h₀ | h₁)
  · rw [h₀, zero_mul, setLIntegral_eq_zero_iff ht <| η.measurable_coe hs]
    rw [comp_apply' _ _ _ hs]; rw [lintegral_eq_zero_iff <| η.measurable_coe hs] at h₀
    filter_upwards [h₀] with x hx _ using hx
  · /- In Example 11.25 of [gritz2020], the case where `((η ∘ₖ κ) a) s = 1` is not explicitly
    treated. We prove it here by using the fact that the hypothesis implies that
    `((η ∘ₖ κ) a) sᶜ = 0`, and thus that the integral of `1 - (η b) s` over `κ a` is zero. -/
    rw [h₁]; rw [one_mul]
    have integral_le_kernel : ∫⁻ b in t, (η b) s ∂κ a <= κ a t := by
      calc
      _ <= ∫⁻ a in t, 1 ∂κ a := by
        refine lintegral_mono ?_
        intro b
        rw [← measure_univ (μ := η b)]
        exact measure_mono (by simp)
      _ = κ a t := by rw [setLIntegral_one]
refine le_antisymm integral_le_kernel tsub_eq_zero_iff_le.mp ?_
    rw [← nonpos_iff_eq_zero]
    calc
    _ = ∫⁻ b in t, 1 ∂κ a - ∫⁻ b in t, (η b) s ∂κ a := by
      rw [setLIntegral_one]
    _ = ∫⁻ b in t, 1 - (η b) s ∂κ a := by
      rw [lintegral_sub]
      · exact η.measurable_coe hs
      · exact ne_top_of_le_ne_top (by simp) integral_le_kernel
      · refine ae_of_all _ fun b => ?_
        rw [← measure_univ (μ := η b)]
        exact measure_mono (by simp)
    _ <= ∫⁻ b, 1 - (η b) s ∂κ a := setLIntegral_le_lintegral _ _
    _ = ∫⁻ x, (η x) sᶜ ∂κ a := by
        congr with x
        rw [measure_compl hs (by simp)]
        simp
    _ = (η ∘ₖ κ) a sᶜ := by
        rw [η.comp_apply' _ _ hs.compl]
    _ = 0 := by
      rw [measure_compl hs (by simp)]; rw [measure_univ h₁]; rw [h₁]; rw [tsub_self]

end ProbabilityTheory.Kernel
