/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Integrable functions

In this file, the predicate `Integrable` is defined and basic properties of
integrable functions are proved.

Such a predicate is already available under the name `MemLp 1`. We give a direct definition which
is easier to use, and show that it is equivalent to `MemLp 1`.

## Main definition

* Let `f : α → β` be a function, where `α` is a `MeasureSpace` and `β` a `NormedAddCommGroup`
  which also a `MeasurableSpace`. Then `f` is called `Integrable` if
  `f` is `Measurable` and `HasFiniteIntegral f` holds.

## Implementation notes

To prove something for an arbitrary integrable function, a useful theorem is
`Integrable.induction` in the file `SetIntegral`.

## Tags

integrable

-/

@[expose] public section


noncomputable section

open EMetric ENNReal Filter MeasureTheory NNReal Set TopologicalSpace

open scoped Topology

variable {α β γ δ ε ε' ε'' : Type*} {m : MeasurableSpace α} {μ ν : Measure α} [MeasurableSpace δ]
variable [NormedAddCommGroup β] [NormedAddCommGroup γ]
  [TopologicalSpace ε] [ContinuousENorm ε] [TopologicalSpace ε'] [ContinuousENorm ε'] [ENorm ε'']

namespace MeasureTheory

/-! ### The predicate `Integrable` -/

/-- `Integrable f μ` means that `f` is measurable and that the integral `∫⁻ a, ‖f a‖ ∂μ` is finite.
  `Integrable f` means `Integrable f volume`. -/
@[fun_prop, wikidata Q3153745]
/--
Definition of `Integrable` / `Integrable` 的定义

English:
definition Integrable
  signature: {α} {_ : MeasurableSpace α} (f : α -> ε)
  body: AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ

中文:
定义 可积
  签名: {α} {_ : 可测空间 α} (f : α -> ε)
  定义体: AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ

Depends on / 依赖: AEStronglyMeasurable, HasFiniteIntegral, volume_tac
-/
def Integrable {α} {_ : MeasurableSpace α} (f : α -> ε)
    (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ

/-- Notation for `Integrable` with respect to a non-standard σ-algebra. -/
scoped notation "Integrable[" mα "]" => @Integrable _ _ _ _ mα

/--
theorem `memLp_one_iff_integrable` / 定理 `memLp_one_iff_integrable`

English:
theorem memLp_one_iff_integrable
  given: {f : α -> ε}
  statement: MemLp f 1 μ ↔ Integrable f μ
  proof: by
  simp_rw [Integrable, hasFiniteIntegral_iff_enorm, MemLp, eLpNorm_one_eq_lintegral_enorm]

@[fun_prop]

中文:
定理 memLp_one_iff_integrable
  条件: {f : α -> ε}
  结论: MemLp f 1 μ ↔ 可积 f μ
  证明: by
  simp_rw [Integrable, hasFiniteIntegral_iff_enorm, MemLp, eLpNorm_one_eq_lintegral_enorm]

@[fun_prop]

Depends on / 依赖: Integrable, eLpNorm_one_eq_lintegral_enorm, hasFiniteIntegral_iff_enorm, simp_rw
-/
theorem memLp_one_iff_integrable {f : α -> ε} : MemLp f 1 μ ↔ Integrable f μ := by
  simp_rw [Integrable, hasFiniteIntegral_iff_enorm, MemLp, eLpNorm_one_eq_lintegral_enorm]

@[fun_prop]
/--
theorem `Integrable.aestronglyMeasurable` / 定理 `Integrable.aestronglyMeasurable`

English:
theorem Integrable.aestronglyMeasurable
  given: {f : α -> ε} (hf : Integrable f μ)
  proof: hf.1

@[fun_prop]

中文:
定理 可积.aestronglyMeasurable
  条件: {f : α -> ε} (hf : 可积 f μ)
  证明: hf.1

@[fun_prop]
-/
theorem Integrable.aestronglyMeasurable {f : α -> ε} (hf : Integrable f μ) :
    AEStronglyMeasurable f μ :=
  hf.1

@[fun_prop]
/--
theorem `Integrable.aemeasurable` / 定理 `Integrable.aemeasurable`

English:
theorem Integrable.aemeasurable
  statement: [MeasurableSpace ε] [BorelSpace ε] [PseudoMetrizableSpace ε]
  proof: hf.aestronglyMeasurable.aemeasurable

@[fun_prop]

中文:
定理 可积.aemeasurable
  结论: [可测空间 ε] [Borel空间 ε] [PseudoMetrizable空间 ε]
  证明: hf.aestronglyMeasurable.aemeasurable

@[fun_prop]

Depends on / 依赖: _term, aemeasurable, aestronglyMeasurable, hf.aestronglyMeasurable.aemeasurable
-/
theorem Integrable.aemeasurable [MeasurableSpace ε] [BorelSpace ε] [PseudoMetrizableSpace ε]
    {f : α -> ε} (hf : Integrable f μ) : AEMeasurable f μ :=
  hf.aestronglyMeasurable.aemeasurable

@[fun_prop]
/--
theorem `Integrable.hasFiniteIntegral` / 定理 `Integrable.hasFiniteIntegral`

English:
theorem Integrable.hasFiniteIntegral
  given: {f : α -> ε} (hf : Integrable f μ)
  statement: HasFiniteIntegral f μ
  proof: hf.2

中文:
定理 可积.hasFinite整数egral
  条件: {f : α -> ε} (hf : 可积 f μ)
  结论: HasFinite整数egral f μ
  证明: hf.2
-/
theorem Integrable.hasFiniteIntegral {f : α -> ε} (hf : Integrable f μ) : HasFiniteIntegral f μ :=
  hf.2

/--
theorem `Integrable.mono_enorm` / 定理 `Integrable.mono_enorm`

English:
theorem Integrable.mono_enorm
  statement: {f : α -> ε} {g : α -> ε'} (hg : Integrable g μ)
  proof: ⟨hf, hg.hasFiniteIntegral.mono_enorm h⟩

中文:
定理 可积.mono_enorm
  结论: {f : α -> ε} {g : α -> ε'} (hg : 可积 g μ)
  证明: ⟨hf, hg.hasFiniteIntegral.mono_enorm h⟩

Depends on / 依赖: hasFiniteIntegral, hg.hasFiniteIntegral.mono_enorm, mono_enorm
-/
theorem Integrable.mono_enorm {f : α -> ε} {g : α -> ε'} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : forallᵐ a ∂μ, ‖f a‖ₑ <= ‖g a‖ₑ) : Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono_enorm h⟩

/--
theorem `Integrable.mono` / 定理 `Integrable.mono`

English:
theorem Integrable.mono
  statement: {f : α -> β} {g : α -> γ} (hg : Integrable g μ)
  proof: ⟨hf, hg.hasFiniteIntegral.mono h⟩

中文:
定理 可积.mono
  结论: {f : α -> β} {g : α -> γ} (hg : 可积 g μ)
  证明: ⟨hf, hg.hasFiniteIntegral.mono h⟩
-/
theorem Integrable.mono {f : α -> β} {g : α -> γ} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : forallᵐ a ∂μ, ‖f a‖ <= ‖g a‖) : Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono h⟩

/--
theorem `Integrable.mono_nonneg` / 定理 `Integrable.mono_nonneg`

English:
theorem Integrable.mono_nonneg
  statement: [Lattice β] [HasSolidNorm β] [AddLeftMono β] {f g : α -> β}
  proof: ⟨hf, hg.hasFiniteIntegral.mono_nonneg hnonneg h⟩

中文:
定理 可积.mono_nonneg
  结论: [格 β] [有Solid范数 β] [AddLeftMono β] {f g : α -> β}
  证明: ⟨hf, hg.hasFiniteIntegral.mono_nonneg hnonneg h⟩

Depends on / 依赖: hasFiniteIntegral, hg.hasFiniteIntegral.mono_nonneg, hnonneg, mono_nonneg
-/
theorem Integrable.mono_nonneg [Lattice β] [HasSolidNorm β] [AddLeftMono β] {f g : α -> β}
    (hg : Integrable g μ) (hf : AEStronglyMeasurable f μ) (hnonneg : forallᵐ a ∂μ, 0 <= f a)
    (h : forallᵐ a ∂μ, f a <= g a) :
    Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono_nonneg hnonneg h⟩

/--
theorem `Integrable.mono'_enorm` / 定理 `Integrable.mono'_enorm`

English:
theorem Integrable.mono'_enorm
  statement: {f : α -> ε} {g : α -> Real>=0∞} (hg : Integrable g μ)
  proof: ⟨hf, hg.hasFiniteIntegral.mono_enorm h⟩

中文:
定理 可积.mono'_enorm
  结论: {f : α -> ε} {g : α -> 实数>=0∞} (hg : 可积 g μ)
  证明: ⟨hf, hg.hasFiniteIntegral.mono_enorm h⟩

Depends on / 依赖: hasFiniteIntegral, hg.hasFiniteIntegral.mono_enorm, mono_enorm
-/
theorem Integrable.mono'_enorm {f : α -> ε} {g : α -> Real>=0∞} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : forallᵐ a ∂μ, ‖f a‖ₑ <= g a) : Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono_enorm h⟩

/--
theorem `Integrable.mono'` / 定理 `Integrable.mono'`

English:
theorem Integrable.mono'
  statement: {f : α -> β} {g : α -> Real} (hg : Integrable g μ)
  proof: ⟨hf, hg.hasFiniteIntegral.mono' h⟩

中文:
定理 可积.mono'
  结论: {f : α -> β} {g : α -> 实数} (hg : 可积 g μ)
  证明: ⟨hf, hg.hasFiniteIntegral.mono' h⟩

Depends on / 依赖: _term_iff, not_lt, not_lt.mpr, tsum_eq_zero_of_not_summable
-/
theorem Integrable.mono' {f : α -> β} {g : α -> Real} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (h : forallᵐ a ∂μ, ‖f a‖ <= g a) : Integrable f μ :=
  ⟨hf, hg.hasFiniteIntegral.mono' h⟩

/--
theorem `Integrable.congr'_enorm` / 定理 `Integrable.congr'_enorm`

English:
theorem Integrable.congr'_enorm
  statement: {f : α -> ε} {g : α -> ε'} (hf : Integrable f μ)
  proof: ⟨hg, hf.hasFiniteIntegral.congr'_enorm h⟩

中文:
定理 可积.congr'_enorm
  结论: {f : α -> ε} {g : α -> ε'} (hf : 可积 f μ)
  证明: ⟨hg, hf.hasFiniteIntegral.congr'_enorm h⟩

Depends on / 依赖: _enorm, hasFiniteIntegral, hf.hasFiniteIntegral.congr
-/
theorem Integrable.congr'_enorm {f : α -> ε} {g : α -> ε'} (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (h : forallᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : Integrable g μ :=
  ⟨hg, hf.hasFiniteIntegral.congr'_enorm h⟩

/--
theorem `Integrable.congr'` / 定理 `Integrable.congr'`

English:
theorem Integrable.congr'
  statement: {f : α -> β} {g : α -> γ} (hf : Integrable f μ)
  proof: ⟨hg, hf.hasFiniteIntegral.congr' h⟩

中文:
定理 可积.congr'
  结论: {f : α -> β} {g : α -> γ} (hf : 可积 f μ)
  证明: ⟨hg, hf.hasFiniteIntegral.congr' h⟩
-/
theorem Integrable.congr' {f : α -> β} {g : α -> γ} (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (h : forallᵐ a ∂μ, ‖f a‖ = ‖g a‖) : Integrable g μ :=
  ⟨hg, hf.hasFiniteIntegral.congr' h⟩

/--
theorem `integrable_congr'_enorm` / 定理 `integrable_congr'_enorm`

English:
theorem integrable_congr'_enorm
  statement: {f : α -> ε} {g : α -> ε'}
  proof: ⟨fun h2f => h2f.congr'_enorm hg h, fun h2g => h2g.congr'_enorm hf EventuallyEq.symm h⟩

中文:
定理 integrable_congr'_enorm
  结论: {f : α -> ε} {g : α -> ε'}
  证明: ⟨fun h2f => h2f.congr'_enorm hg h, fun h2g => h2g.congr'_enorm hf EventuallyEq.symm h⟩

Depends on / 依赖: EventuallyEq, EventuallyEq.symm, _enorm, h2f.congr, h2g.congr
-/
theorem integrable_congr'_enorm {f : α -> ε} {g : α -> ε'}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (h : forallᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) :
    Integrable f μ ↔ Integrable g μ :=
⟨fun h2f => h2f.congr'_enorm hg h, fun h2g => h2g.congr'_enorm hf EventuallyEq.symm h⟩

/--
theorem `integrable_congr'` / 定理 `integrable_congr'`

English:
theorem integrable_congr'
  statement: {f : α -> β} {g : α -> γ} (hf : AEStronglyMeasurable f μ)
  proof: integrable_congr'_enorm hf hg h.mono fun _x hx => enorm_eq_iff_norm_eq.mpr hx

中文:
定理 integrable_congr'
  结论: {f : α -> β} {g : α -> γ} (hf : AEStronglyMeasurable f μ)
  证明: integrable_congr'_enorm hf hg h.mono fun _x hx => enorm_eq_iff_norm_eq.mpr hx
-/
theorem integrable_congr' {f : α -> β} {g : α -> γ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (h : forallᵐ a ∂μ, ‖f a‖ = ‖g a‖) :
    Integrable f μ ↔ Integrable g μ :=
integrable_congr'_enorm hf hg h.mono fun _x hx => enorm_eq_iff_norm_eq.mpr hx

/--
theorem `Integrable.congr` / 定理 `Integrable.congr`

English:
theorem Integrable.congr
  given: {f g : α -> ε} (hf : Integrable f μ) (h : f =ᵐ[μ] g)
  statement: Integrable g μ
  proof: ⟨hf.1.congr h, hf.2.congr h⟩

中文:
定理 可积.congr
  条件: {f g : α -> ε} (hf : 可积 f μ) (h : f =ᵐ[μ] g)
  结论: 可积 g μ
  证明: ⟨hf.1.congr h, hf.2.congr h⟩
-/
theorem Integrable.congr {f g : α -> ε} (hf : Integrable f μ) (h : f =ᵐ[μ] g) : Integrable g μ :=
  ⟨hf.1.congr h, hf.2.congr h⟩

/--
theorem `integrable_congr` / 定理 `integrable_congr`

English:
theorem integrable_congr
  given: {f g : α -> ε} (h : f =ᵐ[μ] g)
  statement: Integrable f μ ↔ Integrable g μ
  proof: ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

中文:
定理 integrable_congr
  条件: {f g : α -> ε} (h : f =ᵐ[μ] g)
  结论: 可积 f μ ↔ 可积 g μ
  证明: ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

Depends on / 依赖: h.symm, hf.congr, hg.congr
-/
theorem integrable_congr {f g : α -> ε} (h : f =ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

/--
theorem `integrable_const_iff_enorm` / 定理 `integrable_const_iff_enorm`

English:
theorem integrable_const_iff_enorm
  given: {c : ε} (hc : ‖c‖ₑ != ∞)
  proof: by
  have : AEStronglyMeasurable (fun _ : α => c) μ := aestronglyMeasurable_const
  rw [Integrable]; rw [and_iff_right this]; rw [hasFiniteIntegral_const_iff_enorm hc]

中文:
定理 integrable_const_iff_enorm
  条件: {c : ε} (hc : ‖c‖ₑ != ∞)
  证明: by
  have : AEStronglyMeasurable (fun _ : α => c) μ := aestronglyMeasurable_const
  rw [Integrable]; rw [and_iff_right this]; rw [hasFiniteIntegral_const_iff_enorm hc]

Depends on / 依赖: AEStronglyMeasurable, Integrable, aestronglyMeasurable_const, and_iff_right, hasFiniteIntegral_const_iff_enorm
-/
theorem integrable_const_iff_enorm {c : ε} (hc : ‖c‖ₑ != ∞) :
    Integrable (fun _ : α => c) μ ↔ ‖c‖ₑ = 0 ∨ IsFiniteMeasure μ := by
  have : AEStronglyMeasurable (fun _ : α => c) μ := aestronglyMeasurable_const
  rw [Integrable]; rw [and_iff_right this]; rw [hasFiniteIntegral_const_iff_enorm hc]

/--
lemma `integrable_const_iff` / 引理 `integrable_const_iff`

English:
lemma integrable_const_iff
  given: {c : β}
  statement: Integrable (fun _ : α => c) μ ↔ c = 0 ∨ IsFiniteMeasure μ
  proof: by
  rw [integrable_const_iff_enorm enorm_ne_top]
  simp

中文:
引理 integrable_const_iff
  条件: {c : β}
  结论: 可积 (fun _ : α => c) μ ↔ c = 0 ∨ 是有限测度 μ
  证明: by
  rw [integrable_const_iff_enorm enorm_ne_top]
  simp

Depends on / 依赖: enorm_ne_top, integrable_const_iff_enorm
-/
lemma integrable_const_iff {c : β} : Integrable (fun _ : α => c) μ ↔ c = 0 ∨ IsFiniteMeasure μ := by
  rw [integrable_const_iff_enorm enorm_ne_top]
  simp

/--
lemma `integrable_const_iff_isFiniteMeasure_enorm` / 引理 `integrable_const_iff_isFiniteMeasure_enorm`

English:
lemma integrable_const_iff_isFiniteMeasure_enorm
  given: {c : ε} (hc : ‖c‖ₑ != 0) (hc' : ‖c‖ₑ != ∞)
  proof: by
  simp [integrable_const_iff_enorm hc', hc, isFiniteMeasure_iff]

中文:
引理 integrable_const_iff_isFiniteMeasure_enorm
  条件: {c : ε} (hc : ‖c‖ₑ != 0) (hc' : ‖c‖ₑ != ∞)
  证明: by
  simp [integrable_const_iff_enorm hc', hc, isFiniteMeasure_iff]

Depends on / 依赖: integrable_const_iff_enorm, isFiniteMeasure_iff
-/
lemma integrable_const_iff_isFiniteMeasure_enorm {c : ε} (hc : ‖c‖ₑ != 0) (hc' : ‖c‖ₑ != ∞) :
    Integrable (fun _ => c) μ ↔ IsFiniteMeasure μ := by
  simp [integrable_const_iff_enorm hc', hc, isFiniteMeasure_iff]

/--
lemma `integrable_const_iff_isFiniteMeasure` / 引理 `integrable_const_iff_isFiniteMeasure`

English:
lemma integrable_const_iff_isFiniteMeasure
  given: {c : β} (hc : c != 0)
  proof: by
  simp [integrable_const_iff, hc, isFiniteMeasure_iff]

中文:
引理 integrable_const_iff_isFiniteMeasure
  条件: {c : β} (hc : c != 0)
  证明: by
  simp [integrable_const_iff, hc, isFiniteMeasure_iff]

Depends on / 依赖: integrable_const_iff, isFiniteMeasure_iff
-/
lemma integrable_const_iff_isFiniteMeasure {c : β} (hc : c != 0) :
    Integrable (fun _ => c) μ ↔ IsFiniteMeasure μ := by
  simp [integrable_const_iff, hc, isFiniteMeasure_iff]

/--
theorem `Integrable.of_mem_Icc_enorm` / 定理 `Integrable.of_mem_Icc_enorm`

English:
theorem Integrable.of_mem_Icc_enorm
  statement: [IsFiniteMeasure μ]
  proof: ⟨hX.aestronglyMeasurable, .of_mem_Icc_of_ne_top ha hb h⟩

中文:
定理 可积.of_mem_Icc_enorm
  结论: [是有限测度 μ]
  证明: ⟨hX.aestronglyMeasurable, .of_mem_Icc_of_ne_top ha hb h⟩

Depends on / 依赖: aestronglyMeasurable, hX.aestronglyMeasurable, of_mem_Icc_of_ne_top
-/
theorem Integrable.of_mem_Icc_enorm [IsFiniteMeasure μ]
    {a b : Real>=0∞} (ha : a != ∞) (hb : b != ∞) {X : α -> Real>=0∞} (hX : AEMeasurable X μ)
    (h : forallᵐ ω ∂μ, X ω in Set.Icc a b) :
    Integrable X μ :=
  ⟨hX.aestronglyMeasurable, .of_mem_Icc_of_ne_top ha hb h⟩

/--
theorem `Integrable.of_mem_Icc` / 定理 `Integrable.of_mem_Icc`

English:
theorem Integrable.of_mem_Icc
  statement: [IsFiniteMeasure μ] (a b : Real) {X : α -> Real} (hX : AEMeasurable X μ)
  proof: ⟨hX.aestronglyMeasurable, .of_mem_Icc a b h⟩

@[simp, fun_prop]

中文:
定理 可积.of_mem_Icc
  结论: [是有限测度 μ] (a b : 实数) {X : α -> 实数} (hX : 几乎处处可测 X μ)
  证明: ⟨hX.aestronglyMeasurable, .of_mem_Icc a b h⟩

@[simp, fun_prop]

Depends on / 依赖: Complex.exp_add, _term, aestronglyMeasurable, exp_add, exp_int_mul, exp_two_pi_mul_I, hX.aestronglyMeasurable, mul_add, mul_one, of_mem_Icc, one_zpow, simp_rw, tsum_congr
-/
theorem Integrable.of_mem_Icc [IsFiniteMeasure μ] (a b : Real) {X : α -> Real} (hX : AEMeasurable X μ)
    (h : forallᵐ ω ∂μ, X ω in Set.Icc a b) :
    Integrable X μ :=
  ⟨hX.aestronglyMeasurable, .of_mem_Icc a b h⟩

@[simp, fun_prop]
/--
theorem `integrable_const_enorm` / 定理 `integrable_const_enorm`

English:
theorem integrable_const_enorm
  given: [IsFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞)
  proof: (integrable_const_iff_enorm hc).2 .inr ‹_›

@[fun_prop]

中文:
定理 integrable_const_enorm
  条件: [是有限测度 μ] {c : ε} (hc : ‖c‖ₑ != ∞)
  证明: (integrable_const_iff_enorm hc).2 .inr ‹_›

@[fun_prop]

Depends on / 依赖: Complex.exp_add, _term, exp_add, exp_int_mul_two_pi_mul_I, integrable_const_iff_enorm, mul_add, mul_comm, mul_one, tsum_congr
-/
theorem integrable_const_enorm [IsFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞) :
    Integrable (fun _ : α => c) μ :=
(integrable_const_iff_enorm hc).2 .inr ‹_›

@[fun_prop]
/--
theorem `integrable_const` / 定理 `integrable_const`

English:
theorem integrable_const
  given: [IsFiniteMeasure μ] (c : β)
  statement: Integrable (fun _ : α => c) μ
  proof: integrable_const_iff.2 .inr ‹_›

中文:
定理 integrable_const
  条件: [是有限测度 μ] (c : β)
  结论: 可积 (fun _ : α => c) μ
  证明: integrable_const_iff.2 .inr ‹_›

Depends on / 依赖: Complex.exp_add, Int.cast_add, Int.cast_one, _term, _undef, add_sub_cancel_right, cast_add, cast_one, conv_rhs, exp_add, integrable_const_iff, le_or_gt, mul_add, mul_assoc, mul_comm, mul_one, mul_zero, simp_rw, sub_mul, sub_zero
-/
theorem integrable_const [IsFiniteMeasure μ] (c : β) : Integrable (fun _ : α => c) μ :=
integrable_const_iff.2 .inr ‹_›

-- TODO: an `ENorm`-version of this lemma requires `HasFiniteIntegral.of_finite`
@[fun_prop, simp]
/--
lemma `Integrable.of_finite` / 引理 `Integrable.of_finite`

English:
lemma Integrable.of_finite
  given: [Finite α] [MeasurableSingletonClass α] [IsFiniteMeasure μ] {f : α -> β}
  proof: ⟨.of_discrete, .of_finite⟩

中文:
引理 可积.of_finite
  条件: [有限 α] [MeasurableSingleton类 α] [是有限测度 μ] {f : α -> β}
  证明: ⟨.of_discrete, .of_finite⟩

Depends on / 依赖: Equiv.neg, Equiv.neg_apply, _term, neg_apply, neg_mul, of_discrete, of_finite, ring_nf, tsum_eq, tsum_neg
-/
lemma Integrable.of_finite [Finite α] [MeasurableSingletonClass α] [IsFiniteMeasure μ] {f : α -> β} :
    Integrable f μ := ⟨.of_discrete, .of_finite⟩

/--
lemma `Integrable.of_isEmpty` / 引理 `Integrable.of_isEmpty`

English:
lemma Integrable.of_isEmpty
  given: [IsEmpty α] {f : α -> β}
  statement: Integrable f μ
  proof: .of_finite

中文:
引理 可积.of_isEmpty
  条件: [是空 α] {f : α -> β}
  结论: 可积 f μ
  证明: .of_finite

Depends on / 依赖: Complex.exp_conj, _neg_left, _term, conj_I, conj_ofReal, conj_tsum, exp_conj, map_add, map_mul, map_pow, neg_inj, ofReal_intCast, ofReal_ofNat, of_finite, ring_nf, simp_rw, tsum_neg
-/
lemma Integrable.of_isEmpty [IsEmpty α] {f : α -> β} : Integrable f μ := .of_finite

/--
lemma `Integrable.of_subsingleton` / 引理 `Integrable.of_subsingleton`

English:
lemma Integrable.of_subsingleton
  given: [Subsingleton α] [IsFiniteMeasure μ] {f : α -> β}
  proof: .of_finite

中文:
引理 可积.of_subsingleton
  条件: [子单例 α] [是有限测度 μ] {f : α -> β}
  证明: .of_finite

Depends on / 依赖: of_finite
-/
lemma Integrable.of_subsingleton [Subsingleton α] [IsFiniteMeasure μ] {f : α -> β} :
    Integrable f μ :=
  .of_finite

/--
theorem `MemLp.integrable_enorm_rpow` / 定理 `MemLp.integrable_enorm_rpow`

English:
theorem MemLp.integrable_enorm_rpow
  statement: {f : α -> ε} {p : Real>=0∞} (hf : MemLp f p μ) (hp_ne_zero : p != 0)
  proof: by
  rw [← memLp_one_iff_integrable]
  exact hf.enorm_rpow hp_ne_zero hp_ne_top

中文:
定理 MemLp.integrable_enorm_rpow
  结论: {f : α -> ε} {p : 实数>=0∞} (hf : MemLp f p μ) (hp_ne_zero : p != 0)
  证明: by
  rw [← memLp_one_iff_integrable]
  exact hf.enorm_rpow hp_ne_zero hp_ne_top

Depends on / 依赖: HasDerivAt, _undef, div_eq_mul_inv, div_nonneg, div_pos, enorm_rpow, hf.enorm_rpow, hp_ne_top, hp_ne_zero, inv_im, le_or_gt, lt_irrefl, memLp_one_iff_integrable, mul_zero, neg_div, neg_im, neg_neg, neg_nonneg, neg_nonneg.mpr, neg_nonpos
-/
theorem MemLp.integrable_enorm_rpow {f : α -> ε} {p : Real>=0∞} (hf : MemLp f p μ) (hp_ne_zero : p != 0)
    (hp_ne_top : p != ∞) : Integrable (fun x : α => ‖f x‖ₑ ^ p.toReal) μ := by
  rw [← memLp_one_iff_integrable]
  exact hf.enorm_rpow hp_ne_zero hp_ne_top

/--
theorem `MemLp.integrable_norm_rpow` / 定理 `MemLp.integrable_norm_rpow`

English:
theorem MemLp.integrable_norm_rpow
  statement: {f : α -> β} {p : Real>=0∞} (hf : MemLp f p μ) (hp_ne_zero : p != 0)
  proof: by
  rw [← memLp_one_iff_integrable]
  exact hf.norm_rpow hp_ne_zero hp_ne_top

中文:
定理 MemLp.integrable_norm_rpow
  结论: {f : α -> β} {p : 实数>=0∞} (hf : MemLp f p μ) (hp_ne_zero : p != 0)
  证明: by
  rw [← memLp_one_iff_integrable]
  exact hf.norm_rpow hp_ne_zero hp_ne_top

Depends on / 依赖: hf.norm_rpow, hp_ne_top, hp_ne_zero, memLp_one_iff_integrable, norm_rpow
-/
theorem MemLp.integrable_norm_rpow {f : α -> β} {p : Real>=0∞} (hf : MemLp f p μ) (hp_ne_zero : p != 0)
    (hp_ne_top : p != ∞) : Integrable (fun x : α => ‖f x‖ ^ p.toReal) μ := by
  rw [← memLp_one_iff_integrable]
  exact hf.norm_rpow hp_ne_zero hp_ne_top

/--
theorem `MemLp.integrable_enorm_rpow'` / 定理 `MemLp.integrable_enorm_rpow'`

English:
theorem MemLp.integrable_enorm_rpow'
  given: [IsFiniteMeasure μ] {f : α -> ε} {p : Real>=0∞} (hf : MemLp f p μ)
  proof: by
  by_cases h_zero : p = 0
  · simp [h_zero]
  by_cases h_top : p = ∞
  · simp [h_top]
  exact hf.integrable_enorm_rpow h_zero h_top

中文:
定理 MemLp.integrable_enorm_rpow'
  条件: [是有限测度 μ] {f : α -> ε} {p : 实数>=0∞} (hf : MemLp f p μ)
  证明: by
  by_cases h_zero : p = 0
  · simp [h_zero]
  by_cases h_top : p = ∞
  · simp [h_top]
  exact hf.integrable_enorm_rpow h_zero h_top

Depends on / 依赖: h_top, h_zero, hf.integrable_enorm_rpow, integrable_enorm_rpow
-/
theorem MemLp.integrable_enorm_rpow' [IsFiniteMeasure μ] {f : α -> ε} {p : Real>=0∞} (hf : MemLp f p μ) :
    Integrable (fun x : α => ‖f x‖ₑ ^ p.toReal) μ := by
  by_cases h_zero : p = 0
  · simp [h_zero]
  by_cases h_top : p = ∞
  · simp [h_top]
  exact hf.integrable_enorm_rpow h_zero h_top

/--
theorem `MemLp.integrable_norm_rpow'` / 定理 `MemLp.integrable_norm_rpow'`

English:
theorem MemLp.integrable_norm_rpow'
  given: [IsFiniteMeasure μ] {f : α -> β} {p : Real>=0∞} (hf : MemLp f p μ)
  proof: by
  by_cases h_zero : p = 0
  · simp [h_zero]
  by_cases h_top : p = ∞
  · simp [h_top]
  exact hf.integrable_norm_rpow h_zero h_top

中文:
定理 MemLp.integrable_norm_rpow'
  条件: [是有限测度 μ] {f : α -> β} {p : 实数>=0∞} (hf : MemLp f p μ)
  证明: by
  by_cases h_zero : p = 0
  · simp [h_zero]
  by_cases h_top : p = ∞
  · simp [h_top]
  exact hf.integrable_norm_rpow h_zero h_top

Depends on / 依赖: h_top, h_zero, hf.integrable_norm_rpow, integrable_norm_rpow
-/
theorem MemLp.integrable_norm_rpow' [IsFiniteMeasure μ] {f : α -> β} {p : Real>=0∞} (hf : MemLp f p μ) :
    Integrable (fun x : α => ‖f x‖ ^ p.toReal) μ := by
  by_cases h_zero : p = 0
  · simp [h_zero]
  by_cases h_top : p = ∞
  · simp [h_top]
  exact hf.integrable_norm_rpow h_zero h_top

/--
lemma `MemLp.integrable_enorm_pow` / 引理 `MemLp.integrable_enorm_pow`

English:
lemma MemLp.integrable_enorm_pow
  given: {f : α -> ε} {p : Nat} (hf : MemLp f p μ) (hp : p != 0)
  proof: by
  simpa using hf.integrable_enorm_rpow (mod_cast hp) (by simp)

中文:
引理 MemLp.integrable_enorm_pow
  条件: {f : α -> ε} {p : 自然数} (hf : MemLp f p μ) (hp : p != 0)
  证明: by
  simpa using hf.integrable_enorm_rpow (mod_cast hp) (by simp)

Depends on / 依赖: hf.integrable_enorm_rpow, integrable_enorm_rpow, mod_cast
-/
lemma MemLp.integrable_enorm_pow {f : α -> ε} {p : Nat} (hf : MemLp f p μ) (hp : p != 0) :
    Integrable (fun x : α => ‖f x‖ₑ ^ p) μ := by
  simpa using hf.integrable_enorm_rpow (mod_cast hp) (by simp)

/--
lemma `MemLp.integrable_norm_pow` / 引理 `MemLp.integrable_norm_pow`

English:
lemma MemLp.integrable_norm_pow
  given: {f : α -> β} {p : Nat} (hf : MemLp f p μ) (hp : p != 0)
  proof: by
  simpa using hf.integrable_norm_rpow (mod_cast hp) (by simp)

中文:
引理 MemLp.integrable_norm_pow
  条件: {f : α -> β} {p : 自然数} (hf : MemLp f p μ) (hp : p != 0)
  证明: by
  simpa using hf.integrable_norm_rpow (mod_cast hp) (by simp)

Depends on / 依赖: hf.integrable_norm_rpow, integrable_norm_rpow, mod_cast
-/
lemma MemLp.integrable_norm_pow {f : α -> β} {p : Nat} (hf : MemLp f p μ) (hp : p != 0) :
    Integrable (fun x : α => ‖f x‖ ^ p) μ := by
  simpa using hf.integrable_norm_rpow (mod_cast hp) (by simp)

/--
lemma `MemLp.integrable_enorm_pow'` / 引理 `MemLp.integrable_enorm_pow'`

English:
lemma MemLp.integrable_enorm_pow'
  given: [IsFiniteMeasure μ] {f : α -> ε} {p : Nat} (hf : MemLp f p μ)
  proof: by simpa using hf.integrable_enorm_rpow'

中文:
引理 MemLp.integrable_enorm_pow'
  条件: [是有限测度 μ] {f : α -> ε} {p : 自然数} (hf : MemLp f p μ)
  证明: by simpa using hf.integrable_enorm_rpow'

Depends on / 依赖: hf.integrable_enorm_rpow, integrable_enorm_rpow
-/
lemma MemLp.integrable_enorm_pow' [IsFiniteMeasure μ] {f : α -> ε} {p : Nat} (hf : MemLp f p μ) :
    Integrable (fun x : α => ‖f x‖ₑ ^ p) μ := by simpa using hf.integrable_enorm_rpow'

/--
lemma `MemLp.integrable_norm_pow'` / 引理 `MemLp.integrable_norm_pow'`

English:
lemma MemLp.integrable_norm_pow'
  given: [IsFiniteMeasure μ] {f : α -> β} {p : Nat} (hf : MemLp f p μ)
  proof: by simpa using hf.integrable_norm_rpow'

中文:
引理 MemLp.integrable_norm_pow'
  条件: [是有限测度 μ] {f : α -> β} {p : 自然数} (hf : MemLp f p μ)
  证明: by simpa using hf.integrable_norm_rpow'

Depends on / 依赖: hf.integrable_norm_rpow, integrable_norm_rpow
-/
lemma MemLp.integrable_norm_pow' [IsFiniteMeasure μ] {f : α -> β} {p : Nat} (hf : MemLp f p μ) :
    Integrable (fun x : α => ‖f x‖ ^ p) μ := by simpa using hf.integrable_norm_rpow'

/--
lemma `integrable_enorm_rpow_iff` / 引理 `integrable_enorm_rpow_iff`

English:
lemma integrable_enorm_rpow_iff
  statement: {f : α -> ε} {p : Real>=0∞}
  proof: by
  rw [← memLp_enorm_rpow_iff (q := p) hf p_zero p_top]; rw [← memLp_one_iff_integrable]; rw [ENNReal.div_self p_zero p_top]

中文:
引理 integrable_enorm_rpow_iff
  结论: {f : α -> ε} {p : 实数>=0∞}
  证明: by
  rw [← memLp_enorm_rpow_iff (q := p) hf p_zero p_top]; rw [← memLp_one_iff_integrable]; rw [ENNReal.div_self p_zero p_top]

Depends on / 依赖: ENNReal, ENNReal.div_self, div_self, memLp_enorm_rpow_iff, memLp_one_iff_integrable, p_top, p_zero
-/
lemma integrable_enorm_rpow_iff {f : α -> ε} {p : Real>=0∞}
    (hf : AEStronglyMeasurable f μ) (p_zero : p != 0) (p_top : p != ∞) :
    Integrable (fun x : α => ‖f x‖ₑ ^ p.toReal) μ ↔ MemLp f p μ := by
  rw [← memLp_enorm_rpow_iff (q := p) hf p_zero p_top]; rw [← memLp_one_iff_integrable]; rw [ENNReal.div_self p_zero p_top]

/--
lemma `integrable_norm_rpow_iff` / 引理 `integrable_norm_rpow_iff`

English:
lemma integrable_norm_rpow_iff
  statement: {f : α -> β} {p : Real>=0∞}
  proof: by
  rw [← memLp_norm_rpow_iff (q := p) hf p_zero p_top]; rw [← memLp_one_iff_integrable]; rw [ENNReal.div_self p_zero p_top]

中文:
引理 integrable_norm_rpow_iff
  结论: {f : α -> β} {p : 实数>=0∞}
  证明: by
  rw [← memLp_norm_rpow_iff (q := p) hf p_zero p_top]; rw [← memLp_one_iff_integrable]; rw [ENNReal.div_self p_zero p_top]

Depends on / 依赖: ENNReal, ENNReal.div_self, div_self, memLp_norm_rpow_iff, memLp_one_iff_integrable, p_top, p_zero
-/
lemma integrable_norm_rpow_iff {f : α -> β} {p : Real>=0∞}
    (hf : AEStronglyMeasurable f μ) (p_zero : p != 0) (p_top : p != ∞) :
    Integrable (fun x : α => ‖f x‖ ^ p.toReal) μ ↔ MemLp f p μ := by
  rw [← memLp_norm_rpow_iff (q := p) hf p_zero p_top]; rw [← memLp_one_iff_integrable]; rw [ENNReal.div_self p_zero p_top]

/--
lemma `integrable_norm_rpow_of_le` / 引理 `integrable_norm_rpow_of_le`

English:
lemma integrable_norm_rpow_of_le
  statement: [IsFiniteMeasure μ] {f : α -> β} (hf : AEStronglyMeasurable f μ)
  proof: by
  rcases hp.eq_or_lt with (rfl | hp)
  · simp
  rcases hq.eq_or_lt with (rfl | hq)
  · grind
  rw [← ENNReal.toReal_ofReal hp.le]; rw [integrable_norm_rpow_iff hf (by simp [hp]) (by simp)]
  rw [← ENNReal.toReal_ofReal hq.le]; rw [integrable_norm_rpow_iff hf (by simp [hq]) (by simp)] at hint
  exact MemLp.mono_exponent hint (ENNReal.ofReal_le_ofReal hpq)

中文:
引理 integrable_norm_rpow_of_le
  结论: [是有限测度 μ] {f : α -> β} (hf : AEStronglyMeasurable f μ)
  证明: by
  rcases hp.eq_or_lt with (rfl | hp)
  · simp
  rcases hq.eq_or_lt with (rfl | hq)
  · grind
  rw [← ENNReal.toReal_ofReal hp.le]; rw [integrable_norm_rpow_iff hf (by simp [hp]) (by simp)]
  rw [← ENNReal.toReal_ofReal hq.le]; rw [integrable_norm_rpow_iff hf (by simp [hq]) (by simp)] at hint
  exact MemLp.mono_exponent hint (ENNReal.ofReal_le_ofReal hpq)

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal, ENNReal.toReal_ofReal, MemLp.mono_exponent, eq_or_lt, hp.eq_or_lt, hp.le, hq.eq_or_lt, hq.le, integrable_norm_rpow_iff, mono_exponent, ofReal_le_ofReal, toReal_ofReal
-/
lemma integrable_norm_rpow_of_le [IsFiniteMeasure μ] {f : α -> β} (hf : AEStronglyMeasurable f μ)
    {p q : Real} (hp : 0 <= p) (hq : 0 <= q) (hpq : p <= q) (hint : Integrable (fun x => ‖f x‖ ^ q) μ) :
    Integrable (fun x => ‖f x‖ ^ p) μ := by
  rcases hp.eq_or_lt with (rfl | hp)
  · simp
  rcases hq.eq_or_lt with (rfl | hq)
  · grind
  rw [← ENNReal.toReal_ofReal hp.le]; rw [integrable_norm_rpow_iff hf (by simp [hp]) (by simp)]
  rw [← ENNReal.toReal_ofReal hq.le]; rw [integrable_norm_rpow_iff hf (by simp [hq]) (by simp)] at hint
  exact MemLp.mono_exponent hint (ENNReal.ofReal_le_ofReal hpq)

/--
lemma `integrable_norm_pow_of_le` / 引理 `integrable_norm_pow_of_le`

English:
lemma integrable_norm_pow_of_le
  statement: [IsFiniteMeasure μ] {f : α -> β} (hf : AEStronglyMeasurable f μ)
  proof: by
  simp_rw [← Real.rpow_natCast] at *
  exact integrable_norm_rpow_of_le hf p.cast_nonneg q.cast_nonneg (by simpa) hint

中文:
引理 integrable_norm_pow_of_le
  结论: [是有限测度 μ] {f : α -> β} (hf : AEStronglyMeasurable f μ)
  证明: by
  simp_rw [← Real.rpow_natCast] at *
  exact integrable_norm_rpow_of_le hf p.cast_nonneg q.cast_nonneg (by simpa) hint

Depends on / 依赖: Real.rpow_natCast, cast_nonneg, integrable_norm_rpow_of_le, p.cast_nonneg, q.cast_nonneg, rpow_natCast, simp_rw
-/
lemma integrable_norm_pow_of_le [IsFiniteMeasure μ] {f : α -> β} (hf : AEStronglyMeasurable f μ)
    {p q : Nat} (hpq : p <= q) (hint : Integrable (fun x => ‖f x‖ ^ q) μ) :
    Integrable (fun x => ‖f x‖ ^ p) μ := by
  simp_rw [← Real.rpow_natCast] at *
  exact integrable_norm_rpow_of_le hf p.cast_nonneg q.cast_nonneg (by simpa) hint

/--
theorem `Integrable.mono_measure` / 定理 `Integrable.mono_measure`

English:
theorem Integrable.mono_measure
  given: {f : α -> ε} (h : Integrable f ν) (hμ : μ <= ν)
  statement: Integrable f μ
  proof: ⟨h.aestronglyMeasurable.mono_measure hμ, h.hasFiniteIntegral.mono_measure hμ⟩

中文:
定理 可积.mono_measure
  条件: {f : α -> ε} (h : 可积 f ν) (hμ : μ <= ν)
  结论: 可积 f μ
  证明: ⟨h.aestronglyMeasurable.mono_measure hμ, h.hasFiniteIntegral.mono_measure hμ⟩

Depends on / 依赖: aestronglyMeasurable, h.aestronglyMeasurable.mono_measure, h.hasFiniteIntegral.mono_measure, hasFiniteIntegral, mono_measure
-/
theorem Integrable.mono_measure {f : α -> ε} (h : Integrable f ν) (hμ : μ <= ν) : Integrable f μ :=
  ⟨h.aestronglyMeasurable.mono_measure hμ, h.hasFiniteIntegral.mono_measure hμ⟩

/--
theorem `Integrable.of_measure_le_smul` / 定理 `Integrable.of_measure_le_smul`

English:
theorem Integrable.of_measure_le_smul
  statement: {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  proof: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.of_measure_le_smul hc hμ'_le

@[fun_prop]

中文:
定理 可积.of_measure_le_smul
  结论: {ε} [拓扑空间 ε] [ESeminormedAdd幺半群 ε]
  证明: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.of_measure_le_smul hc hμ'_le

@[fun_prop]

Depends on / 依赖: hf.of_measure_le_smul, memLp_one_iff_integrable, of_measure_le_smul
-/
theorem Integrable.of_measure_le_smul {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    {μ' : Measure α} {c : Real>=0∞} (hc : c != ∞) (hμ'_le : μ' <= c • μ)
    {f : α -> ε} (hf : Integrable f μ) : Integrable f μ' := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.of_measure_le_smul hc hμ'_le

@[fun_prop]
/--
theorem `Integrable.add_measure` / 定理 `Integrable.add_measure`

English:
theorem Integrable.add_measure
  statement: [PseudoMetrizableSpace ε]
  proof: by
  simp_rw [← memLp_one_iff_integrable] at hμ hν ⊢
  refine ⟨hμ.aestronglyMeasurable.add_measure hν.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_one_add_measure]; rw [ENNReal.add_lt_top]
  exact ⟨hμ.eLpNorm_lt_top, hν.eLpNorm_lt_top⟩

中文:
定理 可积.add_measure
  结论: [PseudoMetrizable空间 ε]
  证明: by
  simp_rw [← memLp_one_iff_integrable] at hμ hν ⊢
  refine ⟨hμ.aestronglyMeasurable.add_measure hν.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_one_add_measure]; rw [ENNReal.add_lt_top]
  exact ⟨hμ.eLpNorm_lt_top, hν.eLpNorm_lt_top⟩

Depends on / 依赖: ENNReal, ENNReal.add_lt_top, add_lt_top, add_measure, aestronglyMeasurable, aestronglyMeasurable.add_measure, eLpNorm_lt_top, eLpNorm_one_add_measure, memLp_one_iff_integrable, simp_rw
-/
theorem Integrable.add_measure [PseudoMetrizableSpace ε]
    {f : α -> ε} (hμ : Integrable f μ) (hν : Integrable f ν) :
    Integrable f (μ + ν) := by
  simp_rw [← memLp_one_iff_integrable] at hμ hν ⊢
  refine ⟨hμ.aestronglyMeasurable.add_measure hν.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_one_add_measure]; rw [ENNReal.add_lt_top]
  exact ⟨hμ.eLpNorm_lt_top, hν.eLpNorm_lt_top⟩

/--
theorem `Integrable.left_of_add_measure` / 定理 `Integrable.left_of_add_measure`

English:
theorem Integrable.left_of_add_measure
  given: {f : α -> ε} (h : Integrable f (μ + ν))
  statement: Integrable f μ
  proof: by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.left_of_add_measure

中文:
定理 可积.left_of_add_measure
  条件: {f : α -> ε} (h : 可积 f (μ + ν))
  结论: 可积 f μ
  证明: by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.left_of_add_measure

Depends on / 依赖: h.left_of_add_measure, left_of_add_measure, memLp_one_iff_integrable
-/
theorem Integrable.left_of_add_measure {f : α -> ε} (h : Integrable f (μ + ν)) : Integrable f μ := by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.left_of_add_measure

/--
theorem `Integrable.right_of_add_measure` / 定理 `Integrable.right_of_add_measure`

English:
theorem Integrable.right_of_add_measure
  given: {f : α -> ε} (h : Integrable f (μ + ν))
  proof: by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.right_of_add_measure

@[simp]

中文:
定理 可积.right_of_add_measure
  条件: {f : α -> ε} (h : 可积 f (μ + ν))
  证明: by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.right_of_add_measure

@[simp]

Depends on / 依赖: h.right_of_add_measure, memLp_one_iff_integrable, right_of_add_measure
-/
theorem Integrable.right_of_add_measure {f : α -> ε} (h : Integrable f (μ + ν)) :
    Integrable f ν := by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.right_of_add_measure

@[simp]
/--
theorem `integrable_add_measure` / 定理 `integrable_add_measure`

English:
theorem integrable_add_measure
  given: [PseudoMetrizableSpace ε] {f : α -> ε}
  proof: ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩

@[simp]

中文:
定理 integrable_add_measure
  条件: [PseudoMetrizable空间 ε] {f : α -> ε}
  证明: ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩

@[simp]

Depends on / 依赖: add_measure, h.left_of_add_measure, h.right_of_add_measure, left_of_add_measure, right_of_add_measure
-/
theorem integrable_add_measure [PseudoMetrizableSpace ε] {f : α -> ε} :
    Integrable f (μ + ν) ↔ Integrable f μ ∧ Integrable f ν :=
  ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩

@[simp]
/--
theorem `integrable_zero_measure` / 定理 `integrable_zero_measure`

English:
theorem integrable_zero_measure
  given: {f : α -> ε}
  statement: Integrable f (0 : Measure α)
  proof: by
  constructor <;> fun_prop

中文:
定理 integrable_zero_measure
  条件: {f : α -> ε}
  结论: 可积 f (0 : 测度 α)
  证明: by
  constructor <;> fun_prop

Depends on / 依赖: fun_prop
-/
theorem integrable_zero_measure {f : α -> ε} : Integrable f (0 : Measure α) := by
  constructor <;> fun_prop

/-- In a measurable space with measurable singletons, every function is integrable with respect to
a Dirac measure.
See `integrable_dirac'` for a version which requires `f` to be strongly measurable but does not
need singletons to be measurable. -/
@[fun_prop]
/--
lemma `integrable_dirac` / 引理 `integrable_dirac`

English:
lemma integrable_dirac
  given: [MeasurableSingletonClass α] {a : α} {f : α -> ε} (hfa : ‖f a‖ₑ < ∞)
  proof: ⟨aestronglyMeasurable_dirac, by simpa [HasFiniteIntegral]⟩

中文:
引理 integrable_dirac
  条件: [MeasurableSingleton类 α] {a : α} {f : α -> ε} (hfa : ‖f a‖ₑ < ∞)
  证明: ⟨aestronglyMeasurable_dirac, by simpa [HasFiniteIntegral]⟩

Depends on / 依赖: HasFiniteIntegral, aestronglyMeasurable_dirac
-/
lemma integrable_dirac [MeasurableSingletonClass α] {a : α} {f : α -> ε} (hfa : ‖f a‖ₑ < ∞) :
    Integrable f (Measure.dirac a) :=
  ⟨aestronglyMeasurable_dirac, by simpa [HasFiniteIntegral]⟩

/-- Every strongly measurable function is integrable with respect to a Dirac measure.
See `integrable_dirac` for a version which requires that singletons are measurable sets but has no
hypothesis on `f`. -/
@[fun_prop]
/--
lemma `integrable_dirac'` / 引理 `integrable_dirac'`

English:
lemma integrable_dirac'
  given: {a : α} {f : α -> ε} (hf : StronglyMeasurable f) (hfa : ‖f a‖ₑ < ∞)
  proof: ⟨hf.aestronglyMeasurable, by simpa [HasFiniteIntegral, lintegral_dirac' _ hf.enorm]⟩

中文:
引理 integrable_dirac'
  条件: {a : α} {f : α -> ε} (hf : StronglyMeasurable f) (hfa : ‖f a‖ₑ < ∞)
  证明: ⟨hf.aestronglyMeasurable, by simpa [HasFiniteIntegral, lintegral_dirac' _ hf.enorm]⟩

Depends on / 依赖: HasFiniteIntegral, aestronglyMeasurable, hf.aestronglyMeasurable, hf.enorm, lintegral_dirac
-/
lemma integrable_dirac' {a : α} {f : α -> ε} (hf : StronglyMeasurable f) (hfa : ‖f a‖ₑ < ∞) :
    Integrable f (Measure.dirac a) :=
  ⟨hf.aestronglyMeasurable, by simpa [HasFiniteIntegral, lintegral_dirac' _ hf.enorm]⟩

/--
theorem `integrable_finsetSum_measure` / 定理 `integrable_finsetSum_measure`

English:
theorem integrable_finsetSum_measure
  statement: [PseudoMetrizableSpace ε]
  proof: by
  classical
  induction s using Finset.induction_on <;> simp [*]

@[deprecated (since := "2026-04-08")]
alias integrable_finset_sum_measure := integrable_finsetSum_measure

中文:
定理 integrable_finsetSum_measure
  结论: [PseudoMetrizable空间 ε]
  证明: by
  classical
  induction s using Finset.induction_on <;> simp [*]

@[deprecated (since := "2026-04-08")]
alias integrable_finset_sum_measure := integrable_finsetSum_measure

Depends on / 依赖: Finset, Finset.induction_on, classical, induction_on
-/
theorem integrable_finsetSum_measure [PseudoMetrizableSpace ε]
    {ι} {m : MeasurableSpace α} {f : α -> ε} {μ : ι -> Measure α}
    {s : Finset ι} : Integrable f (∑ i in s, μ i) ↔ forall i in s, Integrable f (μ i) := by
  classical
  induction s using Finset.induction_on <;> simp [*]

@[deprecated (since := "2026-04-08")]
alias integrable_finset_sum_measure := integrable_finsetSum_measure

section

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

@[fun_prop]
/--
theorem `Integrable.smul_measure` / 定理 `Integrable.smul_measure`

English:
theorem Integrable.smul_measure
  given: {f : α -> ε} (h : Integrable f μ) {c : Real>=0∞} (hc : c != ∞)
  proof: by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.smul_measure hc

@[fun_prop]

中文:
定理 可积.smul_measure
  条件: {f : α -> ε} (h : 可积 f μ) {c : 实数>=0∞} (hc : c != ∞)
  证明: by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.smul_measure hc

@[fun_prop]

Depends on / 依赖: h.smul_measure, memLp_one_iff_integrable, smul_measure
-/
theorem Integrable.smul_measure {f : α -> ε} (h : Integrable f μ) {c : Real>=0∞} (hc : c != ∞) :
    Integrable f (c • μ) := by
  rw [← memLp_one_iff_integrable] at h ⊢
  exact h.smul_measure hc

@[fun_prop]
/--
theorem `Integrable.smul_measure_nnreal` / 定理 `Integrable.smul_measure_nnreal`

English:
theorem Integrable.smul_measure_nnreal
  given: {f : α -> ε} (h : Integrable f μ) {c : Real>=0}
  proof: by
  apply h.smul_measure
  simp

中文:
定理 可积.smul_measure_nnreal
  条件: {f : α -> ε} (h : 可积 f μ) {c : 实数>=0}
  证明: by
  apply h.smul_measure
  simp

Depends on / 依赖: h.smul_measure, smul_measure
-/
theorem Integrable.smul_measure_nnreal {f : α -> ε} (h : Integrable f μ) {c : Real>=0} :
    Integrable f (c • μ) := by
  apply h.smul_measure
  simp

/--
theorem `integrable_smul_measure` / 定理 `integrable_smul_measure`

English:
theorem integrable_smul_measure
  given: {f : α -> ε} {c : Real>=0∞} (h₁ : c != 0) (h₂ : c != ∞)
  proof: ⟨fun h => by
    simpa only [smul_smul, ENNReal.inv_mul_cancel h₁ h₂, one_smul] using
      h.smul_measure (ENNReal.inv_ne_top.2 h₁),
    fun h => h.smul_measure h₂⟩

中文:
定理 integrable_smul_measure
  条件: {f : α -> ε} {c : 实数>=0∞} (h₁ : c != 0) (h₂ : c != ∞)
  证明: ⟨fun h => by
    simpa only [smul_smul, ENNReal.inv_mul_cancel h₁ h₂, one_smul] using
      h.smul_measure (ENNReal.inv_ne_top.2 h₁),
    fun h => h.smul_measure h₂⟩

Depends on / 依赖: ENNReal, ENNReal.inv_mul_cancel, ENNReal.inv_ne_top, h.smul_measure, inv_mul_cancel, inv_ne_top, one_smul, smul_measure, smul_smul
-/
theorem integrable_smul_measure {f : α -> ε} {c : Real>=0∞} (h₁ : c != 0) (h₂ : c != ∞) :
    Integrable f (c • μ) ↔ Integrable f μ :=
  ⟨fun h => by
    simpa only [smul_smul, ENNReal.inv_mul_cancel h₁ h₂, one_smul] using
      h.smul_measure (ENNReal.inv_ne_top.2 h₁),
    fun h => h.smul_measure h₂⟩

/--
theorem `integrable_inv_smul_measure` / 定理 `integrable_inv_smul_measure`

English:
theorem integrable_inv_smul_measure
  given: {f : α -> ε} {c : Real>=0∞} (h₁ : c != 0) (h₂ : c != ∞)
  proof: integrable_smul_measure (by simpa using h₂) (by simpa using h₁)

中文:
定理 integrable_inv_smul_measure
  条件: {f : α -> ε} {c : 实数>=0∞} (h₁ : c != 0) (h₂ : c != ∞)
  证明: integrable_smul_measure (by simpa using h₂) (by simpa using h₁)

Depends on / 依赖: integrable_smul_measure
-/
theorem integrable_inv_smul_measure {f : α -> ε} {c : Real>=0∞} (h₁ : c != 0) (h₂ : c != ∞) :
    Integrable f (c⁻¹ • μ) ↔ Integrable f μ :=
  integrable_smul_measure (by simpa using h₂) (by simpa using h₁)

/--
theorem `Integrable.to_average` / 定理 `Integrable.to_average`

English:
theorem Integrable.to_average
  given: {f : α -> ε} (h : Integrable f μ)
  statement: Integrable f ((μ univ)⁻¹ • μ)
  proof: by
  rcases eq_or_ne μ 0 with (rfl | hne)
  · rwa [smul_zero]
  · apply h.smul_measure
    simpa

中文:
定理 可积.to_average
  条件: {f : α -> ε} (h : 可积 f μ)
  结论: 可积 f ((μ univ)⁻¹ • μ)
  证明: by
  rcases eq_or_ne μ 0 with (rfl | hne)
  · rwa [smul_zero]
  · apply h.smul_measure
    simpa

Depends on / 依赖: eq_or_ne, h.smul_measure, smul_measure, smul_zero
-/
theorem Integrable.to_average {f : α -> ε} (h : Integrable f μ) : Integrable f ((μ univ)⁻¹ • μ) := by
  rcases eq_or_ne μ 0 with (rfl | hne)
  · rwa [smul_zero]
  · apply h.smul_measure
    simpa

/--
theorem `integrable_average` / 定理 `integrable_average`

English:
theorem integrable_average
  given: [IsFiniteMeasure μ] {f : α -> ε}
  proof: by
  classical
  exact (eq_or_ne μ 0).by_cases (fun h => by simp [h]) fun h =>
    integrable_smul_measure (ENNReal.inv_ne_zero.2 <| by finiteness)
      (ENNReal.inv_ne_top.2 <| mt Measure.measure_univ_eq_zero.1 h)

中文:
定理 integrable_average
  条件: [是有限测度 μ] {f : α -> ε}
  证明: by
  classical
  exact (eq_or_ne μ 0).by_cases (fun h => by simp [h]) fun h =>
    integrable_smul_measure (ENNReal.inv_ne_zero.2 <| by finiteness)
      (ENNReal.inv_ne_top.2 <| mt Measure.measure_univ_eq_zero.1 h)

Depends on / 依赖: ENNReal, ENNReal.inv_ne_top, ENNReal.inv_ne_zero, Measure, Measure.measure_univ_eq_zero, classical, eq_or_ne, finiteness, integrable_smul_measure, inv_ne_top, inv_ne_zero, measure_univ_eq_zero
-/
theorem integrable_average [IsFiniteMeasure μ] {f : α -> ε} :
    Integrable f ((μ univ)⁻¹ • μ) ↔ Integrable f μ := by
  classical
  exact (eq_or_ne μ 0).by_cases (fun h => by simp [h]) fun h =>
    integrable_smul_measure (ENNReal.inv_ne_zero.2 <| by finiteness)
      (ENNReal.inv_ne_top.2 <| mt Measure.measure_univ_eq_zero.1 h)

end

section

variable {α' : Type*} [MeasurableSpace α']

/--
theorem `integrable_map_measure` / 定理 `integrable_map_measure`

English:
theorem integrable_map_measure
  statement: {f : α -> α'} {g : α' -> ε}
  proof: by
  simp_rw [← memLp_one_iff_integrable]
  exact memLp_map_measure_iff hg hf

中文:
定理 integrable_map_measure
  结论: {f : α -> α'} {g : α' -> ε}
  证明: by
  simp_rw [← memLp_one_iff_integrable]
  exact memLp_map_measure_iff hg hf

Depends on / 依赖: memLp_map_measure_iff, memLp_one_iff_integrable, simp_rw
-/
theorem integrable_map_measure {f : α -> α'} {g : α' -> ε}
    (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ := by
  simp_rw [← memLp_one_iff_integrable]
  exact memLp_map_measure_iff hg hf

/--
theorem `Integrable.comp_aemeasurable` / 定理 `Integrable.comp_aemeasurable`

English:
theorem Integrable.comp_aemeasurable
  statement: {f : α -> α'} {g : α' -> ε}
  proof: (integrable_map_measure hg.aestronglyMeasurable hf).mp hg

中文:
定理 可积.comp_aemeasurable
  结论: {f : α -> α'} {g : α' -> ε}
  证明: (integrable_map_measure hg.aestronglyMeasurable hf).mp hg

Depends on / 依赖: aestronglyMeasurable, hg.aestronglyMeasurable, integrable_map_measure
-/
theorem Integrable.comp_aemeasurable {f : α -> α'} {g : α' -> ε}
    (hg : Integrable g (Measure.map f μ)) (hf : AEMeasurable f μ) : Integrable (g ∘ f) μ :=
  (integrable_map_measure hg.aestronglyMeasurable hf).mp hg

/--
theorem `Integrable.comp_measurable` / 定理 `Integrable.comp_measurable`

English:
theorem Integrable.comp_measurable
  statement: {f : α -> α'} {g : α' -> ε} (hg : Integrable g (Measure.map f μ))
  proof: hg.comp_aemeasurable hf.aemeasurable

中文:
定理 可积.comp_measurable
  结论: {f : α -> α'} {g : α' -> ε} (hg : 可积 g (测度.map f μ))
  证明: hg.comp_aemeasurable hf.aemeasurable

Depends on / 依赖: aemeasurable, comp_aemeasurable, hf.aemeasurable, hg.comp_aemeasurable
-/
theorem Integrable.comp_measurable {f : α -> α'} {g : α' -> ε} (hg : Integrable g (Measure.map f μ))
    (hf : Measurable f) : Integrable (g ∘ f) μ :=
  hg.comp_aemeasurable hf.aemeasurable

end

/--
theorem `_root_.MeasurableEmbedding.integrable_map_iff` / 定理 `_root_.MeasurableEmbedding.integrable_map_iff`

English:
theorem _root_.MeasurableEmbedding.integrable_map_iff
  statement: {f : α -> δ} (hf : MeasurableEmbedding f)
  proof: by
  simp_rw [← memLp_one_iff_integrable]
  exact hf.memLp_map_measure_iff

中文:
定理 _root_.可测嵌入.integrable_map_iff
  结论: {f : α -> δ} (hf : 可测嵌入 f)
  证明: by
  simp_rw [← memLp_one_iff_integrable]
  exact hf.memLp_map_measure_iff

Depends on / 依赖: hf.memLp_map_measure_iff, memLp_map_measure_iff, memLp_one_iff_integrable, simp_rw
-/
theorem _root_.MeasurableEmbedding.integrable_map_iff {f : α -> δ} (hf : MeasurableEmbedding f)
    {g : δ -> ε} : Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ := by
  simp_rw [← memLp_one_iff_integrable]
  exact hf.memLp_map_measure_iff

/--
theorem `integrable_map_equiv` / 定理 `integrable_map_equiv`

English:
theorem integrable_map_equiv
  given: (f : α ≃ᵐ δ) (g : δ -> ε)
  proof: by
  simp_rw [← memLp_one_iff_integrable]
  exact f.memLp_map_measure_iff

中文:
定理 integrable_map_equiv
  条件: (f : α ≃ᵐ δ) (g : δ -> ε)
  证明: by
  simp_rw [← memLp_one_iff_integrable]
  exact f.memLp_map_measure_iff

Depends on / 依赖: Cardinal, Cardinal.aleph0_pos, Cardinal.natCast_lt_aleph0, FiniteDimensional, Int.even_or_odd, Module, Module.rank_lt_aleph0_iff, aleph0_pos, dimension_level_one, even_or_odd, f.memLp_map_measure_iff, hk_even, hk_neg, hk_nonneg, hk_odd, levelOne_neg_weight_rank_zero, levelOne_odd_weight_rank_zero, lt_or_ge, memLp_map_measure_iff, memLp_one_iff_integrable
-/
theorem integrable_map_equiv (f : α ≃ᵐ δ) (g : δ -> ε) :
    Integrable g (Measure.map f μ) ↔ Integrable (g ∘ f) μ := by
  simp_rw [← memLp_one_iff_integrable]
  exact f.memLp_map_measure_iff

/--
theorem `MeasurePreserving.integrable_comp` / 定理 `MeasurePreserving.integrable_comp`

English:
theorem MeasurePreserving.integrable_comp
  statement: {ν : Measure δ} {g : δ -> ε} {f : α -> δ}
  proof: by
  rw [← hf.map_eq] at hg ⊢
  exact (integrable_map_measure hg hf.measurable.aemeasurable).symm

中文:
定理 保测.integrable_comp
  结论: {ν : 测度 δ} {g : δ -> ε} {f : α -> δ}
  证明: by
  rw [← hf.map_eq] at hg ⊢
  exact (integrable_map_measure hg hf.measurable.aemeasurable).symm

Depends on / 依赖: aemeasurable, hf.map_eq, hf.measurable.aemeasurable, integrable_map_measure, map_eq, measurable
-/
theorem MeasurePreserving.integrable_comp {ν : Measure δ} {g : δ -> ε} {f : α -> δ}
    (hf : MeasurePreserving f μ ν) (hg : AEStronglyMeasurable g ν) :
    Integrable (g ∘ f) μ ↔ Integrable g ν := by
  rw [← hf.map_eq] at hg ⊢
  exact (integrable_map_measure hg hf.measurable.aemeasurable).symm

/--
theorem `MeasurePreserving.integrable_comp_of_integrable` / 定理 `MeasurePreserving.integrable_comp_of_integrable`

English:
theorem MeasurePreserving.integrable_comp_of_integrable
  statement: {ν : Measure δ} {g : δ -> ε} {f : α -> δ}
  proof: .mpr hg hf.integrable_comp hg.aestronglyMeasurable

中文:
定理 保测.integrable_comp_of_integrable
  结论: {ν : 测度 δ} {g : δ -> ε} {f : α -> δ}
  证明: .mpr hg hf.integrable_comp hg.aestronglyMeasurable

Depends on / 依赖: aestronglyMeasurable, hf.integrable_comp, hg.aestronglyMeasurable, integrable_comp
-/
theorem MeasurePreserving.integrable_comp_of_integrable {ν : Measure δ} {g : δ -> ε} {f : α -> δ}
    (hf : MeasurePreserving f μ ν) (hg : Integrable g ν) :
    Integrable (g ∘ f) μ :=
.mpr hg hf.integrable_comp hg.aestronglyMeasurable

/--
theorem `MeasurePreserving.integrable_comp_emb` / 定理 `MeasurePreserving.integrable_comp_emb`

English:
theorem MeasurePreserving.integrable_comp_emb
  statement: {f : α -> δ} {ν} (h₁ : MeasurePreserving f μ ν)
  proof: h₁.map_eq ▸ Iff.symm h₂.integrable_map_iff

中文:
定理 保测.integrable_comp_emb
  结论: {f : α -> δ} {ν} (h₁ : 保测 f μ ν)
  证明: h₁.map_eq ▸ Iff.symm h₂.integrable_map_iff

Depends on / 依赖: Iff.symm, integrable_map_iff, map_eq
-/
theorem MeasurePreserving.integrable_comp_emb {f : α -> δ} {ν} (h₁ : MeasurePreserving f μ ν)
    (h₂ : MeasurableEmbedding f) {g : δ -> ε} : Integrable (g ∘ f) μ ↔ Integrable g ν :=
  h₁.map_eq ▸ Iff.symm h₂.integrable_map_iff

/--
theorem `lintegral_edist_lt_top` / 定理 `lintegral_edist_lt_top`

English:
theorem lintegral_edist_lt_top
  given: {f g : α -> β} (hf : Integrable f μ) (hg : Integrable g μ)
  proof: lt_of_le_of_lt (lintegral_edist_triangle hf.aestronglyMeasurable aestronglyMeasurable_zero)
    (ENNReal.add_lt_top.2 <| by
      simp_rw [Pi.zero_apply, ← hasFiniteIntegral_iff_edist]
      exact ⟨hf.hasFiniteIntegral, hg.hasFiniteIntegral⟩)

中文:
定理 lintegral_edist_lt_top
  条件: {f g : α -> β} (hf : 可积 f μ) (hg : 可积 g μ)
  证明: lt_of_le_of_lt (lintegral_edist_triangle hf.aestronglyMeasurable aestronglyMeasurable_zero)
    (ENNReal.add_lt_top.2 <| by
      simp_rw [Pi.zero_apply, ← hasFiniteIntegral_iff_edist]
      exact ⟨hf.hasFiniteIntegral, hg.hasFiniteIntegral⟩)

Depends on / 依赖: ENNReal, ENNReal.add_lt_top, Pi.zero_apply, add_lt_top, aestronglyMeasurable, aestronglyMeasurable_zero, hasFiniteIntegral, hasFiniteIntegral_iff_edist, hf.aestronglyMeasurable, hf.hasFiniteIntegral, hg.hasFiniteIntegral, lintegral_edist_triangle, lt_of_le_of_lt, simp_rw, zero_apply
-/
theorem lintegral_edist_lt_top {f g : α -> β} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫⁻ a, edist (f a) (g a) ∂μ) < ∞ :=
  lt_of_le_of_lt (lintegral_edist_triangle hf.aestronglyMeasurable aestronglyMeasurable_zero)
    (ENNReal.add_lt_top.2 <| by
      simp_rw [Pi.zero_apply, ← hasFiniteIntegral_iff_edist]
      exact ⟨hf.hasFiniteIntegral, hg.hasFiniteIntegral⟩)

section ESeminormedAddMonoid

variable {ε' : Type*} [TopologicalSpace ε'] [ESeminormedAddMonoid ε']

variable (α ε') in
@[to_fun (attr := fun_prop, simp) integrable_fun_zero]
/--
theorem `integrable_zero` / 定理 `integrable_zero`

English:
theorem integrable_zero
  given: (μ : Measure α)
  statement: Integrable (0 : α -> ε') μ
  proof: by
  simp [Integrable, aestronglyMeasurable_zero]

中文:
定理 integrable_zero
  条件: (μ : 测度 α)
  结论: 可积 (0 : α -> ε') μ
  证明: by
  simp [Integrable, aestronglyMeasurable_zero]

Depends on / 依赖: Integrable, aestronglyMeasurable_zero
-/
theorem integrable_zero (μ : Measure α) : Integrable (0 : α -> ε') μ := by
  simp [Integrable, aestronglyMeasurable_zero]

/--
theorem `Integrable.add'` / 定理 `Integrable.add'`

English:
theorem Integrable.add'
  given: {f g : α -> ε'} (hf : Integrable f μ) (hg : Integrable g μ)
  proof: calc
    ∫⁻ a, ‖f a + g a‖ₑ ∂μ <= ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ := lintegral_mono fun _ => enorm_add_le _ _
    _ = _ := lintegral_enorm_add_left hf.aestronglyMeasurable _
    _ < ∞ := add_lt_top.2 ⟨hf.hasFiniteIntegral, hg.hasFiniteIntegral⟩

@[to_fun (attr := fun_prop)]

中文:
定理 可积.add'
  条件: {f g : α -> ε'} (hf : 可积 f μ) (hg : 可积 g μ)
  证明: calc
    ∫⁻ a, ‖f a + g a‖ₑ ∂μ <= ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ := lintegral_mono fun _ => enorm_add_le _ _
    _ = _ := lintegral_enorm_add_left hf.aestronglyMeasurable _
    _ < ∞ := add_lt_top.2 ⟨hf.hasFiniteIntegral, hg.hasFiniteIntegral⟩

@[to_fun (attr := fun_prop)]

Depends on / 依赖: add_lt_top, aestronglyMeasurable, enorm_add_le, hasFiniteIntegral, hf.aestronglyMeasurable, hf.hasFiniteIntegral, hg.hasFiniteIntegral, lintegral_enorm_add_left, lintegral_mono
-/
theorem Integrable.add' {f g : α -> ε'} (hf : Integrable f μ) (hg : Integrable g μ) :
    HasFiniteIntegral (f + g) μ :=
  calc
    ∫⁻ a, ‖f a + g a‖ₑ ∂μ <= ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ := lintegral_mono fun _ => enorm_add_le _ _
    _ = _ := lintegral_enorm_add_left hf.aestronglyMeasurable _
    _ < ∞ := add_lt_top.2 ⟨hf.hasFiniteIntegral, hg.hasFiniteIntegral⟩

@[to_fun (attr := fun_prop)]
/--
theorem `Integrable.add` / 定理 `Integrable.add`

English:
theorem Integrable.add
  statement: [ContinuousAdd ε']
  proof: ⟨hf.aestronglyMeasurable.add hg.aestronglyMeasurable, hf.add' hg⟩

@[deprecated (since := "2026-03-19")] alias Integrable.add'' := Integrable.fun_add

@[simp]

中文:
定理 可积.add
  结论: [连续加法 ε']
  证明: ⟨hf.aestronglyMeasurable.add hg.aestronglyMeasurable, hf.add' hg⟩

@[deprecated (since := "2026-03-19")] alias Integrable.add'' := Integrable.fun_add

@[simp]
-/
theorem Integrable.add [ContinuousAdd ε']
    {f g : α -> ε'} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (f + g) μ :=
  ⟨hf.aestronglyMeasurable.add hg.aestronglyMeasurable, hf.add' hg⟩

@[deprecated (since := "2026-03-19")] alias Integrable.add'' := Integrable.fun_add

@[simp]
/--
lemma `Integrable.of_subsingleton_codomain` / 引理 `Integrable.of_subsingleton_codomain`

English:
lemma Integrable.of_subsingleton_codomain
  given: [Subsingleton ε'] {f : α -> ε'}
  proof: .congr .of_forall fun _ => Subsingleton.elim _ _ integrable_zero _ _ _

中文:
引理 可积.of_subsingleton_codomain
  条件: [子单例 ε'] {f : α -> ε'}
  证明: .congr .of_forall fun _ => Subsingleton.elim _ _ integrable_zero _ _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim, integrable_zero, of_forall
-/
lemma Integrable.of_subsingleton_codomain [Subsingleton ε'] {f : α -> ε'} :
    Integrable f μ :=
.congr .of_forall fun _ => Subsingleton.elim _ _ integrable_zero _ _ _

end ESeminormedAddMonoid

section ESeminormedAddCommMonoid

variable {ε' : Type*} [TopologicalSpace ε'] [ESeminormedAddCommMonoid ε'] [ContinuousAdd ε']

@[fun_prop]
/--
theorem `integrable_finsetSum'` / 定理 `integrable_finsetSum'`

English:
theorem integrable_finsetSum'
  statement: {ι} (s : Finset ι) {f : ι -> α -> ε'}
  proof: Finset.sum_induction f (fun g => Integrable g μ) (fun _ _ => Integrable.add)
    (integrable_zero _ _ _) hf

@[deprecated (since := "2026-04-08")] alias integrable_finset_sum' := integrable_finsetSum'

@[fun_prop]

中文:
定理 integrable_finsetSum'
  结论: {ι} (s : 有限集 ι) {f : ι -> α -> ε'}
  证明: Finset.sum_induction f (fun g => Integrable g μ) (fun _ _ => Integrable.add)
    (integrable_zero _ _ _) hf

@[deprecated (since := "2026-04-08")] alias integrable_finset_sum' := integrable_finsetSum'

@[fun_prop]

Depends on / 依赖: Finset, Finset.sum_induction, Integrable, Integrable.add, integrable_zero, sum_induction
-/
theorem integrable_finsetSum' {ι} (s : Finset ι) {f : ι -> α -> ε'}
    (hf : forall i in s, Integrable (f i) μ) : Integrable (∑ i in s, f i) μ :=
  Finset.sum_induction f (fun g => Integrable g μ) (fun _ _ => Integrable.add)
    (integrable_zero _ _ _) hf

@[deprecated (since := "2026-04-08")] alias integrable_finset_sum' := integrable_finsetSum'

@[fun_prop]
/--
theorem `integrable_finsetSum` / 定理 `integrable_finsetSum`

English:
theorem integrable_finsetSum
  statement: {ι} (s : Finset ι) {f : ι -> α -> ε'}
  proof: by
  simpa only [← Finset.sum_apply] using integrable_finsetSum' s hf

@[deprecated (since := "2026-04-08")] alias integrable_finset_sum := integrable_finsetSum

中文:
定理 integrable_finsetSum
  结论: {ι} (s : 有限集 ι) {f : ι -> α -> ε'}
  证明: by
  simpa only [← Finset.sum_apply] using integrable_finsetSum' s hf

@[deprecated (since := "2026-04-08")] alias integrable_finset_sum := integrable_finsetSum

Depends on / 依赖: Finset, Finset.sum_apply, integrable_finsetSum, sum_apply
-/
theorem integrable_finsetSum {ι} (s : Finset ι) {f : ι -> α -> ε'}
    (hf : forall i in s, Integrable (f i) μ) : Integrable (fun a => ∑ i in s, f i a) μ := by
  simpa only [← Finset.sum_apply] using integrable_finsetSum' s hf

@[deprecated (since := "2026-04-08")] alias integrable_finset_sum := integrable_finsetSum

end ESeminormedAddCommMonoid

/-- If `f` is integrable, then so is `-f`. -/
@[to_fun (attr := fun_prop)]
/--
theorem `Integrable.neg` / 定理 `Integrable.neg`

English:
theorem Integrable.neg
  given: {f : α -> β} (hf : Integrable f μ)
  statement: Integrable (-f) μ
  proof: ⟨hf.aestronglyMeasurable.neg, by fun_prop⟩

@[deprecated (since := "2026-03-19")] alias Integrable.neg' := Integrable.fun_neg

@[simp]

中文:
定理 可积.neg
  条件: {f : α -> β} (hf : 可积 f μ)
  结论: 可积 (-f) μ
  证明: ⟨hf.aestronglyMeasurable.neg, by fun_prop⟩

@[deprecated (since := "2026-03-19")] alias Integrable.neg' := Integrable.fun_neg

@[simp]
-/
theorem Integrable.neg {f : α -> β} (hf : Integrable f μ) : Integrable (-f) μ :=
  ⟨hf.aestronglyMeasurable.neg, by fun_prop⟩

@[deprecated (since := "2026-03-19")] alias Integrable.neg' := Integrable.fun_neg

@[simp]
/--
theorem `integrable_neg_iff` / 定理 `integrable_neg_iff`

English:
theorem integrable_neg_iff
  given: {f : α -> β}
  statement: Integrable (-f) μ ↔ Integrable f μ
  proof: ⟨fun h => neg_neg f ▸ h.neg, Integrable.neg⟩

@[simp]

中文:
定理 integrable_neg_iff
  条件: {f : α -> β}
  结论: 可积 (-f) μ ↔ 可积 f μ
  证明: ⟨fun h => neg_neg f ▸ h.neg, Integrable.neg⟩

@[simp]

Depends on / 依赖: Integrable, Integrable.neg, h.neg, neg_neg
-/
theorem integrable_neg_iff {f : α -> β} : Integrable (-f) μ ↔ Integrable f μ :=
  ⟨fun h => neg_neg f ▸ h.neg, Integrable.neg⟩

@[simp]
/--
theorem `integrable_fun_neg_iff` / 定理 `integrable_fun_neg_iff`

English:
theorem integrable_fun_neg_iff
  given: {f : α -> β}
  statement: Integrable (fun x => -f x) μ ↔ Integrable f μ
  proof: integrable_neg_iff

中文:
定理 integrable_fun_neg_iff
  条件: {f : α -> β}
  结论: 可积 (fun x => -f x) μ ↔ 可积 f μ
  证明: integrable_neg_iff

Depends on / 依赖: integrable_neg_iff
-/
theorem integrable_fun_neg_iff {f : α -> β} : Integrable (fun x => -f x) μ ↔ Integrable f μ :=
  integrable_neg_iff

/-- if `f` is integrable, then `f + g` is integrable iff `g` is.
See `integrable_add_iff_integrable_right'` for the same statement with `fun x ↦ f x + g x` instead
of `f + g`. -/
@[simp]
/--
lemma `integrable_add_iff_integrable_right` / 引理 `integrable_add_iff_integrable_right`

English:
lemma integrable_add_iff_integrable_right
  given: {f g : α -> β} (hf : Integrable f μ)
  proof: ⟨fun h => show g = f + g + (-f) by simp only [add_neg_cancel_comm] ▸ h.add hf.neg,
    fun h => hf.add h⟩

中文:
引理 integrable_add_iff_integrable_right
  条件: {f g : α -> β} (hf : 可积 f μ)
  证明: ⟨fun h => show g = f + g + (-f) by simp only [add_neg_cancel_comm] ▸ h.add hf.neg,
    fun h => hf.add h⟩

Depends on / 依赖: add_neg_cancel_comm, h.add, hf.add, hf.neg
-/
lemma integrable_add_iff_integrable_right {f g : α -> β} (hf : Integrable f μ) :
    Integrable (f + g) μ ↔ Integrable g μ :=
  ⟨fun h => show g = f + g + (-f) by simp only [add_neg_cancel_comm] ▸ h.add hf.neg,
    fun h => hf.add h⟩

/-- if `f` is integrable, then `fun x ↦ f x + g x` is integrable iff `g` is.
See `integrable_add_iff_integrable_right` for the same statement with `f + g` instead
of `fun x ↦ f x + g x`. -/
@[simp]
/--
lemma `integrable_add_iff_integrable_right'` / 引理 `integrable_add_iff_integrable_right'`

English:
lemma integrable_add_iff_integrable_right'
  given: {f g : α -> β} (hf : Integrable f μ)
  proof: integrable_add_iff_integrable_right hf

中文:
引理 integrable_add_iff_integrable_right'
  条件: {f g : α -> β} (hf : 可积 f μ)
  证明: integrable_add_iff_integrable_right hf

Depends on / 依赖: integrable_add_iff_integrable_right
-/
lemma integrable_add_iff_integrable_right' {f g : α -> β} (hf : Integrable f μ) :
    Integrable (fun x => f x + g x) μ ↔ Integrable g μ :=
  integrable_add_iff_integrable_right hf

/-- if `f` is integrable, then `g + f` is integrable iff `g` is.
See `integrable_add_iff_integrable_left'` for the same statement with `fun x ↦ g x + f x` instead
of `g + f`. -/
@[simp]
/--
lemma `integrable_add_iff_integrable_left` / 引理 `integrable_add_iff_integrable_left`

English:
lemma integrable_add_iff_integrable_left
  given: {f g : α -> β} (hf : Integrable f μ)
  proof: by
  rw [add_comm]; rw [integrable_add_iff_integrable_right hf]

中文:
引理 integrable_add_iff_integrable_left
  条件: {f g : α -> β} (hf : 可积 f μ)
  证明: by
  rw [add_comm]; rw [integrable_add_iff_integrable_right hf]

Depends on / 依赖: add_comm, integrable_add_iff_integrable_right
-/
lemma integrable_add_iff_integrable_left {f g : α -> β} (hf : Integrable f μ) :
    Integrable (g + f) μ ↔ Integrable g μ := by
  rw [add_comm]; rw [integrable_add_iff_integrable_right hf]

/-- if `f` is integrable, then `fun x ↦ g x + f x` is integrable iff `g` is.
See `integrable_add_iff_integrable_left'` for the same statement with `g + f` instead
of `fun x ↦ g x + f x`. -/
@[simp]
/--
lemma `integrable_add_iff_integrable_left'` / 引理 `integrable_add_iff_integrable_left'`

English:
lemma integrable_add_iff_integrable_left'
  given: {f g : α -> β} (hf : Integrable f μ)
  proof: integrable_add_iff_integrable_left hf

中文:
引理 integrable_add_iff_integrable_left'
  条件: {f g : α -> β} (hf : 可积 f μ)
  证明: integrable_add_iff_integrable_left hf

Depends on / 依赖: integrable_add_iff_integrable_left
-/
lemma integrable_add_iff_integrable_left' {f g : α -> β} (hf : Integrable f μ) :
    Integrable (fun x => g x + f x) μ ↔ Integrable g μ :=
  integrable_add_iff_integrable_left hf

/--
lemma `integrable_left_of_integrable_add_of_nonneg` / 引理 `integrable_left_of_integrable_add_of_nonneg`

English:
lemma integrable_left_of_integrable_add_of_nonneg
  statement: {f g : α -> Real}
  proof: by
  refine h_int.mono' h_meas ?_
  filter_upwards [hf, hg] with a haf hag
  exact (Real.norm_of_nonneg haf).symm ▸ le_add_of_nonneg_right hag

中文:
引理 integrable_left_of_integrable_add_of_nonneg
  结论: {f g : α -> 实数}
  证明: by
  refine h_int.mono' h_meas ?_
  filter_upwards [hf, hg] with a haf hag
  exact (Real.norm_of_nonneg haf).symm ▸ le_add_of_nonneg_right hag

Depends on / 依赖: Real.norm_of_nonneg, filter_upwards, h_int, h_int.mono, h_meas, le_add_of_nonneg_right, norm_of_nonneg
-/
lemma integrable_left_of_integrable_add_of_nonneg {f g : α -> Real}
    (h_meas : AEStronglyMeasurable f μ) (hf : 0 <=ᵐ[μ] f) (hg : 0 <=ᵐ[μ] g)
    (h_int : Integrable (f + g) μ) : Integrable f μ := by
  refine h_int.mono' h_meas ?_
  filter_upwards [hf, hg] with a haf hag
  exact (Real.norm_of_nonneg haf).symm ▸ le_add_of_nonneg_right hag

/--
lemma `integrable_right_of_integrable_add_of_nonneg` / 引理 `integrable_right_of_integrable_add_of_nonneg`

English:
lemma integrable_right_of_integrable_add_of_nonneg
  statement: {f g : α -> Real}
  proof: integrable_left_of_integrable_add_of_nonneg
    ((AEStronglyMeasurable.add_iff_right h_meas).mp h_int.aestronglyMeasurable)
      hg hf (add_comm f g ▸ h_int)

中文:
引理 integrable_right_of_integrable_add_of_nonneg
  结论: {f g : α -> 实数}
  证明: integrable_left_of_integrable_add_of_nonneg
    ((AEStronglyMeasurable.add_iff_right h_meas).mp h_int.aestronglyMeasurable)
      hg hf (add_comm f g ▸ h_int)

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.add_iff_right, add_comm, add_iff_right, aestronglyMeasurable, h_int, h_int.aestronglyMeasurable, h_meas, integrable_left_of_integrable_add_of_nonneg
-/
lemma integrable_right_of_integrable_add_of_nonneg {f g : α -> Real}
    (h_meas : AEStronglyMeasurable f μ) (hf : 0 <=ᵐ[μ] f) (hg : 0 <=ᵐ[μ] g)
    (h_int : Integrable (f + g) μ) : Integrable g μ :=
  integrable_left_of_integrable_add_of_nonneg
    ((AEStronglyMeasurable.add_iff_right h_meas).mp h_int.aestronglyMeasurable)
      hg hf (add_comm f g ▸ h_int)

/--
lemma `integrable_add_iff_of_nonneg` / 引理 `integrable_add_iff_of_nonneg`

English:
lemma integrable_add_iff_of_nonneg
  statement: {f g : α -> Real} (h_meas : AEStronglyMeasurable f μ)
  proof: ⟨fun h => ⟨integrable_left_of_integrable_add_of_nonneg h_meas hf hg h,
    integrable_right_of_integrable_add_of_nonneg h_meas hf hg h⟩, fun ⟨hf, hg⟩ => hf.add hg⟩

中文:
引理 integrable_add_iff_of_nonneg
  结论: {f g : α -> 实数} (h_meas : AEStronglyMeasurable f μ)
  证明: ⟨fun h => ⟨integrable_left_of_integrable_add_of_nonneg h_meas hf hg h,
    integrable_right_of_integrable_add_of_nonneg h_meas hf hg h⟩, fun ⟨hf, hg⟩ => hf.add hg⟩

Depends on / 依赖: h_meas, hf.add, integrable_left_of_integrable_add_of_nonneg, integrable_right_of_integrable_add_of_nonneg
-/
lemma integrable_add_iff_of_nonneg {f g : α -> Real} (h_meas : AEStronglyMeasurable f μ)
    (hf : 0 <=ᵐ[μ] f) (hg : 0 <=ᵐ[μ] g) :
    Integrable (f + g) μ ↔ Integrable f μ ∧ Integrable g μ :=
  ⟨fun h => ⟨integrable_left_of_integrable_add_of_nonneg h_meas hf hg h,
    integrable_right_of_integrable_add_of_nonneg h_meas hf hg h⟩, fun ⟨hf, hg⟩ => hf.add hg⟩

/--
lemma `integrable_add_iff_of_nonpos` / 引理 `integrable_add_iff_of_nonpos`

English:
lemma integrable_add_iff_of_nonpos
  statement: {f g : α -> Real} (h_meas : AEStronglyMeasurable f μ)
  proof: by
  rw [← integrable_neg_iff]; rw [← integrable_neg_iff (f := f)]; rw [← integrable_neg_iff (f := g)]; rw [neg_add]
  exact integrable_add_iff_of_nonneg h_meas.neg (hf.mono (fun _ => neg_nonneg_of_nonpos))
    (hg.mono (fun _ => neg_nonneg_of_nonpos))

中文:
引理 integrable_add_iff_of_nonpos
  结论: {f g : α -> 实数} (h_meas : AEStronglyMeasurable f μ)
  证明: by
  rw [← integrable_neg_iff]; rw [← integrable_neg_iff (f := f)]; rw [← integrable_neg_iff (f := g)]; rw [neg_add]
  exact integrable_add_iff_of_nonneg h_meas.neg (hf.mono (fun _ => neg_nonneg_of_nonpos))
    (hg.mono (fun _ => neg_nonneg_of_nonpos))

Depends on / 依赖: h_meas, h_meas.neg, hf.mono, hg.mono, integrable_add_iff_of_nonneg, integrable_neg_iff, neg_add, neg_nonneg_of_nonpos
-/
lemma integrable_add_iff_of_nonpos {f g : α -> Real} (h_meas : AEStronglyMeasurable f μ)
    (hf : f <=ᵐ[μ] 0) (hg : g <=ᵐ[μ] 0) :
    Integrable (f + g) μ ↔ Integrable f μ ∧ Integrable g μ := by
  rw [← integrable_neg_iff]; rw [← integrable_neg_iff (f := f)]; rw [← integrable_neg_iff (f := g)]; rw [neg_add]
  exact integrable_add_iff_of_nonneg h_meas.neg (hf.mono (fun _ => neg_nonneg_of_nonpos))
    (hg.mono (fun _ => neg_nonneg_of_nonpos))

/--
lemma `integrable_add_const_iff` / 引理 `integrable_add_const_iff`

English:
lemma integrable_add_const_iff
  given: [IsFiniteMeasure μ] {f : α -> β} {c : β}
  proof: integrable_add_iff_integrable_left (integrable_const _)

中文:
引理 integrable_add_const_iff
  条件: [是有限测度 μ] {f : α -> β} {c : β}
  证明: integrable_add_iff_integrable_left (integrable_const _)

Depends on / 依赖: integrable_add_iff_integrable_left, integrable_const
-/
lemma integrable_add_const_iff [IsFiniteMeasure μ] {f : α -> β} {c : β} :
    Integrable (fun x => f x + c) μ ↔ Integrable f μ :=
  integrable_add_iff_integrable_left (integrable_const _)

/--
lemma `integrable_const_add_iff` / 引理 `integrable_const_add_iff`

English:
lemma integrable_const_add_iff
  given: [IsFiniteMeasure μ] {f : α -> β} {c : β}
  proof: integrable_add_iff_integrable_right (integrable_const _)

中文:
引理 integrable_const_add_iff
  条件: [是有限测度 μ] {f : α -> β} {c : β}
  证明: integrable_add_iff_integrable_right (integrable_const _)

Depends on / 依赖: integrable_add_iff_integrable_right, integrable_const
-/
lemma integrable_const_add_iff [IsFiniteMeasure μ] {f : α -> β} {c : β} :
    Integrable (fun x => c + f x) μ ↔ Integrable f μ :=
  integrable_add_iff_integrable_right (integrable_const _)

-- TODO: generalise these lemmas to an `ENormedAddCommSubMonoid`
@[fun_prop]
/--
theorem `Integrable.sub` / 定理 `Integrable.sub`

English:
theorem Integrable.sub
  given: {f g : α -> β} (hf : Integrable f μ) (hg : Integrable g μ)
  proof: by simpa only [sub_eq_add_neg] using hf.add hg.neg

@[fun_prop]

中文:
定理 可积.sub
  条件: {f g : α -> β} (hf : 可积 f μ) (hg : 可积 g μ)
  证明: by simpa only [sub_eq_add_neg] using hf.add hg.neg

@[fun_prop]
-/
theorem Integrable.sub {f g : α -> β} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (f - g) μ := by simpa only [sub_eq_add_neg] using hf.add hg.neg

@[fun_prop]
/--
theorem `Integrable.sub'` / 定理 `Integrable.sub'`

English:
theorem Integrable.sub'
  given: {f g : α -> β} (hf : Integrable f μ) (hg : Integrable g μ)
  proof: by simpa only [sub_eq_add_neg] using! hf.add hg.neg

@[fun_prop]

中文:
定理 可积.sub'
  条件: {f g : α -> β} (hf : 可积 f μ) (hg : 可积 g μ)
  证明: by simpa only [sub_eq_add_neg] using! hf.add hg.neg

@[fun_prop]

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem Integrable.sub' {f g : α -> β} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun a => f a - g a) μ := by simpa only [sub_eq_add_neg] using! hf.add hg.neg

@[fun_prop]
/--
theorem `Integrable.enorm` / 定理 `Integrable.enorm`

English:
theorem Integrable.enorm
  given: {f : α -> ε} (hf : Integrable f μ)
  statement: Integrable (‖f ·‖ₑ) μ
  proof: by
  constructor <;> fun_prop

@[fun_prop]

中文:
定理 可积.enorm
  条件: {f : α -> ε} (hf : 可积 f μ)
  结论: 可积 (‖f ·‖ₑ) μ
  证明: by
  constructor <;> fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop
-/
theorem Integrable.enorm {f : α -> ε} (hf : Integrable f μ) : Integrable (‖f ·‖ₑ) μ := by
  constructor <;> fun_prop

@[fun_prop]
/--
theorem `Integrable.norm` / 定理 `Integrable.norm`

English:
theorem Integrable.norm
  given: {f : α -> β} (hf : Integrable f μ)
  statement: Integrable (fun a => ‖f a‖) μ
  proof: by
  constructor <;> fun_prop

@[fun_prop]

中文:
定理 可积.norm
  条件: {f : α -> β} (hf : 可积 f μ)
  结论: 可积 (fun a => ‖f a‖) μ
  证明: by
  constructor <;> fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop
-/
theorem Integrable.norm {f : α -> β} (hf : Integrable f μ) : Integrable (fun a => ‖f a‖) μ := by
  constructor <;> fun_prop

@[fun_prop]
/--
theorem `Integrable.inf` / 定理 `Integrable.inf`

English:
theorem Integrable.inf
  statement: {β}
  proof: by
  rw [← memLp_one_iff_integrable] at hf hg ⊢
  exact hf.inf hg

@[fun_prop]

中文:
定理 可积.下确界
  结论: {β}
  证明: by
  rw [← memLp_one_iff_integrable] at hf hg ⊢
  exact hf.inf hg

@[fun_prop]

Depends on / 依赖: hf.inf, memLp_one_iff_integrable
-/
theorem Integrable.inf {β}
    [NormedAddCommGroup β] [Lattice β] [HasSolidNorm β] [IsOrderedAddMonoid β]
    {f g : α -> β} (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (f ⊓ g) μ := by
  rw [← memLp_one_iff_integrable] at hf hg ⊢
  exact hf.inf hg

@[fun_prop]
/--
theorem `Integrable.sup` / 定理 `Integrable.sup`

English:
theorem Integrable.sup
  statement: {β}
  proof: by
  rw [← memLp_one_iff_integrable] at hf hg ⊢
  exact hf.sup hg

@[fun_prop]

中文:
定理 可积.上确界
  结论: {β}
  证明: by
  rw [← memLp_one_iff_integrable] at hf hg ⊢
  exact hf.sup hg

@[fun_prop]

Depends on / 依赖: hf.sup, memLp_one_iff_integrable
-/
theorem Integrable.sup {β}
    [NormedAddCommGroup β] [Lattice β] [HasSolidNorm β] [IsOrderedAddMonoid β]
    {f g : α -> β} (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (f ⊔ g) μ := by
  rw [← memLp_one_iff_integrable] at hf hg ⊢
  exact hf.sup hg

@[fun_prop]
/--
theorem `Integrable.abs` / 定理 `Integrable.abs`

English:
theorem Integrable.abs
  statement: {β}
  proof: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.abs

中文:
定理 可积.abs
  结论: {β}
  证明: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.abs

Depends on / 依赖: hf.abs, memLp_one_iff_integrable
-/
theorem Integrable.abs {β}
    [NormedAddCommGroup β] [Lattice β] [HasSolidNorm β] [IsOrderedAddMonoid β]
    {f : α -> β} (hf : Integrable f μ) :
    Integrable (fun a => |f a|) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.abs

-- TODO: generalise the following lemmas to enorm classes

/--
theorem `Integrable.essSup_smul` / 定理 `Integrable.essSup_smul`

English:
theorem Integrable.essSup_smul
  statement: {R : Type*} [NormedRing R] [Module R β] [IsBoundedSMul R β]
  proof: by
  rw [← memLp_one_iff_integrable] at *
  refine ⟨g_aestronglyMeasurable.smul hf.1, ?_⟩
  have hg' : eLpNorm g ∞ μ != ∞ := by rwa [eLpNorm_exponent_top]
  calc
    eLpNorm (fun x : α => g x • f x) 1 μ <= _ := by
      simpa using! MeasureTheory.eLpNorm_smul_le_mul_eLpNorm hf.1 g_aestronglyMeasurable
        (p := ∞) (q := 1)
    _ < ∞ := ENNReal.mul_lt_top hg'.lt_top hf.2

中文:
定理 可积.essSup_smul
  结论: {R : 类型} [赋范环 R] [模 R β] [是BoundedSMul R β]
  证明: by
  rw [← memLp_one_iff_integrable] at *
  refine ⟨g_aestronglyMeasurable.smul hf.1, ?_⟩
  have hg' : eLpNorm g ∞ μ != ∞ := by rwa [eLpNorm_exponent_top]
  calc
    eLpNorm (fun x : α => g x • f x) 1 μ <= _ := by
      simpa using! MeasureTheory.eLpNorm_smul_le_mul_eLpNorm hf.1 g_aestronglyMeasurable
        (p := ∞) (q := 1)
    _ < ∞ := ENNReal.mul_lt_top hg'.lt_top hf.2

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top, MeasureTheory, MeasureTheory.eLpNorm_smul_le_mul_eLpNorm, eLpNorm, eLpNorm_exponent_top, eLpNorm_smul_le_mul_eLpNorm, g_aestronglyMeasurable, g_aestronglyMeasurable.smul, lt_top, memLp_one_iff_integrable, mul_lt_top
-/
theorem Integrable.essSup_smul {R : Type*} [NormedRing R] [Module R β] [IsBoundedSMul R β]
    {f : α -> β} (hf : Integrable f μ) {g : α -> R}
    (g_aestronglyMeasurable : AEStronglyMeasurable g μ) (ess_sup_g : essSup (‖g ·‖ₑ) μ != ∞) :
    Integrable (fun x : α => g x • f x) μ := by
  rw [← memLp_one_iff_integrable] at *
  refine ⟨g_aestronglyMeasurable.smul hf.1, ?_⟩
  have hg' : eLpNorm g ∞ μ != ∞ := by rwa [eLpNorm_exponent_top]
  calc
    eLpNorm (fun x : α => g x • f x) 1 μ <= _ := by
      simpa using! MeasureTheory.eLpNorm_smul_le_mul_eLpNorm hf.1 g_aestronglyMeasurable
        (p := ∞) (q := 1)
    _ < ∞ := ENNReal.mul_lt_top hg'.lt_top hf.2

/--
theorem `Integrable.smul_essSup` / 定理 `Integrable.smul_essSup`

English:
theorem Integrable.smul_essSup
  statement: {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 β]
  proof: by
  rw [← memLp_one_iff_integrable] at *
  refine ⟨hf.1.smul g_aestronglyMeasurable, ?_⟩
  have hg' : eLpNorm g ∞ μ != ∞ := by rwa [eLpNorm_exponent_top]
  calc
    eLpNorm (fun x : α => f x • g x) 1 μ <= _ := by
      simpa using! MeasureTheory.eLpNorm_smul_le_mul_eLpNorm g_aestronglyMeasurable hf.1
        (p := 1) (q := ∞)
    _ < ∞ := ENNReal.mul_lt_top hf.2 hg'.lt_top

中文:
定理 可积.smul_essSup
  结论: {𝕜 : 类型} [赋范环 𝕜] [带零乘法作用 𝕜 β]
  证明: by
  rw [← memLp_one_iff_integrable] at *
  refine ⟨hf.1.smul g_aestronglyMeasurable, ?_⟩
  have hg' : eLpNorm g ∞ μ != ∞ := by rwa [eLpNorm_exponent_top]
  calc
    eLpNorm (fun x : α => f x • g x) 1 μ <= _ := by
      simpa using! MeasureTheory.eLpNorm_smul_le_mul_eLpNorm g_aestronglyMeasurable hf.1
        (p := 1) (q := ∞)
    _ < ∞ := ENNReal.mul_lt_top hf.2 hg'.lt_top

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top, MeasureTheory, MeasureTheory.eLpNorm_smul_le_mul_eLpNorm, eLpNorm, eLpNorm_exponent_top, eLpNorm_smul_le_mul_eLpNorm, g_aestronglyMeasurable, lt_top, memLp_one_iff_integrable, mul_lt_top
-/
theorem Integrable.smul_essSup {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 β]
    [IsBoundedSMul 𝕜 β] {f : α -> 𝕜} (hf : Integrable f μ) {g : α -> β}
    (g_aestronglyMeasurable : AEStronglyMeasurable g μ) (ess_sup_g : essSup (‖g ·‖ₑ) μ != ∞) :
    Integrable (fun x : α => f x • g x) μ := by
  rw [← memLp_one_iff_integrable] at *
  refine ⟨hf.1.smul g_aestronglyMeasurable, ?_⟩
  have hg' : eLpNorm g ∞ μ != ∞ := by rwa [eLpNorm_exponent_top]
  calc
    eLpNorm (fun x : α => f x • g x) 1 μ <= _ := by
      simpa using! MeasureTheory.eLpNorm_smul_le_mul_eLpNorm g_aestronglyMeasurable hf.1
        (p := 1) (q := ∞)
    _ < ∞ := ENNReal.mul_lt_top hf.2 hg'.lt_top

/--
theorem `integrable_enorm_iff` / 定理 `integrable_enorm_iff`

English:
theorem integrable_enorm_iff
  given: {f : α -> ε} (hf : AEStronglyMeasurable f μ)
  proof: by
  simp_rw [Integrable, and_iff_right hf, and_iff_right hf.enorm.aestronglyMeasurable,
    hasFiniteIntegral_enorm_iff]

中文:
定理 integrable_enorm_iff
  条件: {f : α -> ε} (hf : AEStronglyMeasurable f μ)
  证明: by
  simp_rw [Integrable, and_iff_right hf, and_iff_right hf.enorm.aestronglyMeasurable,
    hasFiniteIntegral_enorm_iff]

Depends on / 依赖: Integrable, aestronglyMeasurable, and_iff_right, hasFiniteIntegral_enorm_iff, hf.enorm.aestronglyMeasurable, simp_rw
-/
theorem integrable_enorm_iff {f : α -> ε} (hf : AEStronglyMeasurable f μ) :
    Integrable (‖f ·‖ₑ) μ ↔ Integrable f μ := by
  simp_rw [Integrable, and_iff_right hf, and_iff_right hf.enorm.aestronglyMeasurable,
    hasFiniteIntegral_enorm_iff]

/--
theorem `integrable_norm_iff` / 定理 `integrable_norm_iff`

English:
theorem integrable_norm_iff
  given: {f : α -> β} (hf : AEStronglyMeasurable f μ)
  proof: by
  simp_rw [Integrable, and_iff_right hf, and_iff_right hf.norm, hasFiniteIntegral_norm_iff]

中文:
定理 integrable_norm_iff
  条件: {f : α -> β} (hf : AEStronglyMeasurable f μ)
  证明: by
  simp_rw [Integrable, and_iff_right hf, and_iff_right hf.norm, hasFiniteIntegral_norm_iff]

Depends on / 依赖: Integrable, and_iff_right, hasFiniteIntegral_norm_iff, hf.norm, simp_rw
-/
theorem integrable_norm_iff {f : α -> β} (hf : AEStronglyMeasurable f μ) :
    Integrable (fun a => ‖f a‖) μ ↔ Integrable f μ := by
  simp_rw [Integrable, and_iff_right hf, and_iff_right hf.norm, hasFiniteIntegral_norm_iff]

-- TODO: generalise this lemma to an `ENormedAddCommSubMonoid`
/--
theorem `integrable_of_norm_sub_le` / 定理 `integrable_of_norm_sub_le`

English:
theorem integrable_of_norm_sub_le
  statement: {f₀ f₁ : α -> β} {g : α -> Real} (hf₁_m : AEStronglyMeasurable f₁ μ)
  proof: haveI : forallᵐ a ∂μ, ‖f₁ a‖ <= ‖f₀ a‖ + g a := by
    apply h.mono
    intro a ha
    calc
      ‖f₁ a‖ <= ‖f₀ a‖ + ‖f₀ a - f₁ a‖ := norm_le_insert _ _
      _ <= ‖f₀ a‖ + g a := by gcongr
  Integrable.mono' (hf₀_i.norm.add hg_i) hf₁_m this

中文:
定理 integrable_of_norm_sub_le
  结论: {f₀ f₁ : α -> β} {g : α -> 实数} (hf₁_m : AEStronglyMeasurable f₁ μ)
  证明: haveI : forallᵐ a ∂μ, ‖f₁ a‖ <= ‖f₀ a‖ + g a := by
    apply h.mono
    intro a ha
    calc
      ‖f₁ a‖ <= ‖f₀ a‖ + ‖f₀ a - f₁ a‖ := norm_le_insert _ _
      _ <= ‖f₀ a‖ + g a := by gcongr
  Integrable.mono' (hf₀_i.norm.add hg_i) hf₁_m this

Depends on / 依赖: Integrable, Integrable.mono, _i.norm.add, h.mono, hg_i, norm_le_insert
-/
theorem integrable_of_norm_sub_le {f₀ f₁ : α -> β} {g : α -> Real} (hf₁_m : AEStronglyMeasurable f₁ μ)
    (hf₀_i : Integrable f₀ μ) (hg_i : Integrable g μ) (h : forallᵐ a ∂μ, ‖f₀ a - f₁ a‖ <= g a) :
    Integrable f₁ μ :=
  haveI : forallᵐ a ∂μ, ‖f₁ a‖ <= ‖f₀ a‖ + g a := by
    apply h.mono
    intro a ha
    calc
      ‖f₁ a‖ <= ‖f₀ a‖ + ‖f₀ a - f₁ a‖ := norm_le_insert _ _
      _ <= ‖f₀ a‖ + g a := by gcongr
  Integrable.mono' (hf₀_i.norm.add hg_i) hf₁_m this

/--
lemma `integrable_of_le_of_le` / 引理 `integrable_of_le_of_le`

English:
lemma integrable_of_le_of_le
  statement: {f g₁ g₂ : α -> Real} (hf : AEStronglyMeasurable f μ)
  proof: by
  have : forallᵐ x ∂μ, ‖f x‖ <= max ‖g₁ x‖ ‖g₂ x‖ := by
    filter_upwards [h_le₁, h_le₂] with x hx1 hx2
    simp only [Real.norm_eq_abs]
    exact abs_le_max_abs_abs hx1 hx2
  have h_le_add : forallᵐ x ∂μ, ‖f x‖ <= ‖‖g₁ x‖ + ‖g₂ x‖‖ := by
    filter_upwards [this] with x hx
    refine hx.trans ?_
    conv_rhs => rw [Real.norm_of_nonneg (by positivity)]
    exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
  exact Integrable.mono (by fun_prop) hf h_le_add

中文:
引理 integrable_of_le_of_le
  结论: {f g₁ g₂ : α -> 实数} (hf : AEStronglyMeasurable f μ)
  证明: by
  have : forallᵐ x ∂μ, ‖f x‖ <= max ‖g₁ x‖ ‖g₂ x‖ := by
    filter_upwards [h_le₁, h_le₂] with x hx1 hx2
    simp only [Real.norm_eq_abs]
    exact abs_le_max_abs_abs hx1 hx2
  have h_le_add : forallᵐ x ∂μ, ‖f x‖ <= ‖‖g₁ x‖ + ‖g₂ x‖‖ := by
    filter_upwards [this] with x hx
    refine hx.trans ?_
    conv_rhs => rw [Real.norm_of_nonneg (by positivity)]
    exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
  exact Integrable.mono (by fun_prop) hf h_le_add

Depends on / 依赖: Integrable, Integrable.mono, Real.norm_eq_abs, Real.norm_of_nonneg, abs_le_max_abs_abs, conv_rhs, filter_upwards, fun_prop, h_le_add, hx.trans, max_le_add_of_nonneg, norm_eq_abs, norm_nonneg, norm_of_nonneg
-/
lemma integrable_of_le_of_le {f g₁ g₂ : α -> Real} (hf : AEStronglyMeasurable f μ)
    (h_le₁ : g₁ <=ᵐ[μ] f) (h_le₂ : f <=ᵐ[μ] g₂)
    (h_int₁ : Integrable g₁ μ) (h_int₂ : Integrable g₂ μ) :
    Integrable f μ := by
  have : forallᵐ x ∂μ, ‖f x‖ <= max ‖g₁ x‖ ‖g₂ x‖ := by
    filter_upwards [h_le₁, h_le₂] with x hx1 hx2
    simp only [Real.norm_eq_abs]
    exact abs_le_max_abs_abs hx1 hx2
  have h_le_add : forallᵐ x ∂μ, ‖f x‖ <= ‖‖g₁ x‖ + ‖g₂ x‖‖ := by
    filter_upwards [this] with x hx
    refine hx.trans ?_
    conv_rhs => rw [Real.norm_of_nonneg (by positivity)]
    exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
  exact Integrable.mono (by fun_prop) hf h_le_add

-- TODO: generalising this to enorms requires defining a product instance for enormed monoids first
@[fun_prop]
/--
theorem `Integrable.prodMk` / 定理 `Integrable.prodMk`

English:
theorem Integrable.prodMk
  given: {f : α -> β} {g : α -> γ} (hf : Integrable f μ) (hg : Integrable g μ)
  proof: ⟨by fun_prop,
(hf.norm.add' hg.norm).mono
      Eventually.of_forall fun x =>
        calc
          max ‖f x‖ ‖g x‖ <= ‖f x‖ + ‖g x‖ := max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
          _ <= ‖‖f x‖ + ‖g x‖‖ := le_abs_self _⟩

中文:
定理 可积.prodMk
  条件: {f : α -> β} {g : α -> γ} (hf : 可积 f μ) (hg : 可积 g μ)
  证明: ⟨by fun_prop,
(hf.norm.add' hg.norm).mono
      Eventually.of_forall fun x =>
        calc
          max ‖f x‖ ‖g x‖ <= ‖f x‖ + ‖g x‖ := max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
          _ <= ‖‖f x‖ + ‖g x‖‖ := le_abs_self _⟩

Depends on / 依赖: Eventually, Eventually.of_forall, fun_prop, hf.norm.add, hg.norm, le_abs_self, max_le_add_of_nonneg, norm_nonneg, of_forall
-/
theorem Integrable.prodMk {f : α -> β} {g : α -> γ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => (f x, g x)) μ :=
  ⟨by fun_prop,
(hf.norm.add' hg.norm).mono
      Eventually.of_forall fun x =>
        calc
          max ‖f x‖ ‖g x‖ <= ‖f x‖ + ‖g x‖ := max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
          _ <= ‖‖f x‖ + ‖g x‖‖ := le_abs_self _⟩

/--
theorem `MemLp.integrable` / 定理 `MemLp.integrable`

English:
theorem MemLp.integrable
  statement: {q : Real>=0∞} (hq1 : 1 <= q) {f : α -> ε} [IsFiniteMeasure μ]
  proof: memLp_one_iff_integrable.mp (hfq.mono_exponent hq1)

中文:
定理 MemLp.integrable
  结论: {q : 实数>=0∞} (hq1 : 1 <= q) {f : α -> ε} [是有限测度 μ]
  证明: memLp_one_iff_integrable.mp (hfq.mono_exponent hq1)

Depends on / 依赖: hfq.mono_exponent, memLp_one_iff_integrable, memLp_one_iff_integrable.mp, mono_exponent
-/
theorem MemLp.integrable {q : Real>=0∞} (hq1 : 1 <= q) {f : α -> ε} [IsFiniteMeasure μ]
    (hfq : MemLp f q μ) : Integrable f μ :=
  memLp_one_iff_integrable.mp (hfq.mono_exponent hq1)

/--
theorem `Integrable.measure_enorm_ge_lt_top` / 定理 `Integrable.measure_enorm_ge_lt_top`

English:
theorem Integrable.measure_enorm_ge_lt_top
  statement: {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
  proof: by
  refine meas_ge_le_mul_pow_eLpNorm_enorm μ one_ne_zero one_ne_top hf.1 hε.ne' (by simp [hε'])
.trans_lt ?_
  apply ENNReal.mul_lt_top
  · simpa only [ENNReal.toReal_one, ENNReal.rpow_one, ENNReal.inv_lt_top, ENNReal.ofReal_pos]
      using hε
  · simpa only [ENNReal.toReal_one, ENNReal.rpow_one] using
      (memLp_one_iff_integrable.2 hf).eLpNorm_lt_top

中文:
定理 可积.measure_enorm_ge_lt_top
  结论: {E : 类型} [拓扑空间 E] [余ntinuousE范数 E]
  证明: by
  refine meas_ge_le_mul_pow_eLpNorm_enorm μ one_ne_zero one_ne_top hf.1 hε.ne' (by simp [hε'])
.trans_lt ?_
  apply ENNReal.mul_lt_top
  · simpa only [ENNReal.toReal_one, ENNReal.rpow_one, ENNReal.inv_lt_top, ENNReal.ofReal_pos]
      using hε
  · simpa only [ENNReal.toReal_one, ENNReal.rpow_one] using
      (memLp_one_iff_integrable.2 hf).eLpNorm_lt_top

Depends on / 依赖: ENNReal, ENNReal.inv_lt_top, ENNReal.mul_lt_top, ENNReal.ofReal_pos, ENNReal.rpow_one, ENNReal.toReal_one, eLpNorm_lt_top, inv_lt_top, meas_ge_le_mul_pow_eLpNorm_enorm, memLp_one_iff_integrable, mul_lt_top, ofReal_pos, one_ne_top, one_ne_zero, rpow_one, toReal_one, trans_lt
-/
theorem Integrable.measure_enorm_ge_lt_top {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {f : α -> E} (hf : Integrable f μ) {ε : Real>=0∞} (hε : 0 < ε) (hε' : ε != ∞) :
    μ { x | ε <= ‖f x‖ₑ } < ∞ := by
  refine meas_ge_le_mul_pow_eLpNorm_enorm μ one_ne_zero one_ne_top hf.1 hε.ne' (by simp [hε'])
.trans_lt ?_
  apply ENNReal.mul_lt_top
  · simpa only [ENNReal.toReal_one, ENNReal.rpow_one, ENNReal.inv_lt_top, ENNReal.ofReal_pos]
      using hε
  · simpa only [ENNReal.toReal_one, ENNReal.rpow_one] using
      (memLp_one_iff_integrable.2 hf).eLpNorm_lt_top

/--
theorem `Integrable.measure_norm_ge_lt_top` / 定理 `Integrable.measure_norm_ge_lt_top`

English:
theorem Integrable.measure_norm_ge_lt_top
  given: {f : α -> β} (hf : Integrable f μ) {ε : Real} (hε : 0 < ε)
  proof: by
  convert! Integrable.measure_enorm_ge_lt_top hf (ofReal_pos.mpr hε) ofReal_ne_top with x
  rw [← Real.enorm_of_nonneg hε.le]; rw [enorm_le_iff_norm_le]; rw [Real.norm_of_nonneg hε.le]

中文:
定理 可积.measure_norm_ge_lt_top
  条件: {f : α -> β} (hf : 可积 f μ) {ε : 实数} (hε : 0 < ε)
  证明: by
  convert! Integrable.measure_enorm_ge_lt_top hf (ofReal_pos.mpr hε) ofReal_ne_top with x
  rw [← Real.enorm_of_nonneg hε.le]; rw [enorm_le_iff_norm_le]; rw [Real.norm_of_nonneg hε.le]

Depends on / 依赖: Integrable, Integrable.measure_enorm_ge_lt_top, Real.enorm_of_nonneg, Real.norm_of_nonneg, convert, enorm_le_iff_norm_le, enorm_of_nonneg, measure_enorm_ge_lt_top, norm_of_nonneg, ofReal_ne_top, ofReal_pos, ofReal_pos.mpr
-/
theorem Integrable.measure_norm_ge_lt_top {f : α -> β} (hf : Integrable f μ) {ε : Real} (hε : 0 < ε) :
    μ { x | ε <= ‖f x‖ } < ∞ := by
  convert! Integrable.measure_enorm_ge_lt_top hf (ofReal_pos.mpr hε) ofReal_ne_top with x
  rw [← Real.enorm_of_nonneg hε.le]; rw [enorm_le_iff_norm_le]; rw [Real.norm_of_nonneg hε.le]

/--
lemma `Integrable.measure_norm_gt_lt_top_enorm` / 引理 `Integrable.measure_norm_gt_lt_top_enorm`

English:
lemma Integrable.measure_norm_gt_lt_top_enorm
  statement: {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
  proof: by
  by_cases hε' : ε = ∞
  · simp [hε']
  exact lt_of_le_of_lt (measure_mono (fun _ h => (Set.mem_ofPred_eq ▸ h).le))
    (hf.measure_enorm_ge_lt_top hε hε')

中文:
引理 可积.measure_norm_gt_lt_top_enorm
  结论: {E : 类型} [拓扑空间 E] [余ntinuousE范数 E]
  证明: by
  by_cases hε' : ε = ∞
  · simp [hε']
  exact lt_of_le_of_lt (measure_mono (fun _ h => (Set.mem_ofPred_eq ▸ h).le))
    (hf.measure_enorm_ge_lt_top hε hε')

Depends on / 依赖: Set.mem_ofPred_eq, hf.measure_enorm_ge_lt_top, lt_of_le_of_lt, measure_enorm_ge_lt_top, measure_mono, mem_ofPred_eq
-/
lemma Integrable.measure_norm_gt_lt_top_enorm {E : Type*} [TopologicalSpace E] [ContinuousENorm E]
    {f : α -> E} (hf : Integrable f μ) {ε : Real>=0∞} (hε : 0 < ε) : μ {x | ε < ‖f x‖ₑ} < ∞ := by
  by_cases hε' : ε = ∞
  · simp [hε']
  exact lt_of_le_of_lt (measure_mono (fun _ h => (Set.mem_ofPred_eq ▸ h).le))
    (hf.measure_enorm_ge_lt_top hε hε')

/--
lemma `Integrable.measure_norm_gt_lt_top` / 引理 `Integrable.measure_norm_gt_lt_top`

English:
lemma Integrable.measure_norm_gt_lt_top
  given: {f : α -> β} (hf : Integrable f μ) {ε : Real} (hε : 0 < ε)
  proof: lt_of_le_of_lt (measure_mono (fun _ h => (Set.mem_ofPred_eq ▸ h).le))
    (hf.measure_norm_ge_lt_top hε)

中文:
引理 可积.measure_norm_gt_lt_top
  条件: {f : α -> β} (hf : 可积 f μ) {ε : 实数} (hε : 0 < ε)
  证明: lt_of_le_of_lt (measure_mono (fun _ h => (Set.mem_ofPred_eq ▸ h).le))
    (hf.measure_norm_ge_lt_top hε)

Depends on / 依赖: Set.mem_ofPred_eq, hf.measure_norm_ge_lt_top, lt_of_le_of_lt, measure_mono, measure_norm_ge_lt_top, mem_ofPred_eq
-/
lemma Integrable.measure_norm_gt_lt_top {f : α -> β} (hf : Integrable f μ) {ε : Real} (hε : 0 < ε) :
    μ {x | ε < ‖f x‖} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ h => (Set.mem_ofPred_eq ▸ h).le))
    (hf.measure_norm_ge_lt_top hε)

/--
lemma `Integrable.measure_ge_lt_top` / 引理 `Integrable.measure_ge_lt_top`

English:
lemma Integrable.measure_ge_lt_top
  statement: {f : α -> β} [Lattice β] [HasSolidNorm β] [AddLeftMono β]
  proof: lt_of_le_of_lt (measure_mono fun x hx => norm_le_norm_of_abs_le_abs <|
    (abs_of_nonneg ε_pos.le).symm ▸ hx.trans (le_abs_self (f x)))
    (hf.measure_norm_ge_lt_top (by positivity [ε_pos.ne']))

中文:
引理 可积.measure_ge_lt_top
  结论: {f : α -> β} [格 β] [有Solid范数 β] [AddLeftMono β]
  证明: lt_of_le_of_lt (measure_mono fun x hx => norm_le_norm_of_abs_le_abs <|
    (abs_of_nonneg ε_pos.le).symm ▸ hx.trans (le_abs_self (f x)))
    (hf.measure_norm_ge_lt_top (by positivity [ε_pos.ne']))

Depends on / 依赖: _pos.le, _pos.ne, abs_of_nonneg, hf.measure_norm_ge_lt_top, hx.trans, le_abs_self, lt_of_le_of_lt, measure_mono, measure_norm_ge_lt_top, norm_le_norm_of_abs_le_abs
-/
lemma Integrable.measure_ge_lt_top {f : α -> β} [Lattice β] [HasSolidNorm β] [AddLeftMono β]
    (hf : Integrable f μ) {ε : β} (ε_pos : 0 < ε) :
    μ {a : α | ε <= f a} < ∞ :=
  lt_of_le_of_lt (measure_mono fun x hx => norm_le_norm_of_abs_le_abs <|
    (abs_of_nonneg ε_pos.le).symm ▸ hx.trans (le_abs_self (f x)))
    (hf.measure_norm_ge_lt_top (by positivity [ε_pos.ne']))

/--
lemma `Integrable.measure_le_lt_top` / 引理 `Integrable.measure_le_lt_top`

English:
lemma Integrable.measure_le_lt_top
  statement: {f : α -> β} [Lattice β] [HasSolidNorm β] [AddLeftMono β]
  proof: by
  have : 0 < ‖c‖ := by positivity [c_neg.ne]
  refine lt_of_le_of_lt (measure_mono fun x hx => ?_) (hf.measure_norm_ge_lt_top this)
  have : -c <= -f x := by simp; grind
exact norm_le_norm_of_abs_le_abs abs_of_nonpos c_neg.le ▸ this.trans (neg_le_abs _)

中文:
引理 可积.measure_le_lt_top
  结论: {f : α -> β} [格 β] [有Solid范数 β] [AddLeftMono β]
  证明: by
  have : 0 < ‖c‖ := by positivity [c_neg.ne]
  refine lt_of_le_of_lt (measure_mono fun x hx => ?_) (hf.measure_norm_ge_lt_top this)
  have : -c <= -f x := by simp; grind
exact norm_le_norm_of_abs_le_abs abs_of_nonpos c_neg.le ▸ this.trans (neg_le_abs _)

Depends on / 依赖: abs_of_nonpos, c_neg, c_neg.le, c_neg.ne, hf.measure_norm_ge_lt_top, lt_of_le_of_lt, measure_mono, measure_norm_ge_lt_top, neg_le_abs, norm_le_norm_of_abs_le_abs, this.trans
-/
lemma Integrable.measure_le_lt_top {f : α -> β} [Lattice β] [HasSolidNorm β] [AddLeftMono β]
    (hf : Integrable f μ) {c : β} (c_neg : c < 0) :
    μ {a : α | f a <= c} < ∞ := by
  have : 0 < ‖c‖ := by positivity [c_neg.ne]
  refine lt_of_le_of_lt (measure_mono fun x hx => ?_) (hf.measure_norm_ge_lt_top this)
  have : -c <= -f x := by simp; grind
exact norm_le_norm_of_abs_le_abs abs_of_nonpos c_neg.le ▸ this.trans (neg_le_abs _)

/--
lemma `Integrable.measure_gt_lt_top` / 引理 `Integrable.measure_gt_lt_top`

English:
lemma Integrable.measure_gt_lt_top
  statement: {f : α -> β} [Lattice β] [HasSolidNorm β] [AddLeftMono β]
  proof: lt_of_le_of_lt (measure_mono (fun _ hx => (Set.mem_ofPred_eq ▸ hx).le))
    (Integrable.measure_ge_lt_top hf ε_pos)

中文:
引理 可积.measure_gt_lt_top
  结论: {f : α -> β} [格 β] [有Solid范数 β] [AddLeftMono β]
  证明: lt_of_le_of_lt (measure_mono (fun _ hx => (Set.mem_ofPred_eq ▸ hx).le))
    (Integrable.measure_ge_lt_top hf ε_pos)

Depends on / 依赖: Integrable, Integrable.measure_ge_lt_top, Set.mem_ofPred_eq, lt_of_le_of_lt, measure_ge_lt_top, measure_mono, mem_ofPred_eq
-/
lemma Integrable.measure_gt_lt_top {f : α -> β} [Lattice β] [HasSolidNorm β] [AddLeftMono β]
    (hf : Integrable f μ) {ε : β} (ε_pos : 0 < ε) :
    μ {a : α | ε < f a} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ hx => (Set.mem_ofPred_eq ▸ hx).le))
    (Integrable.measure_ge_lt_top hf ε_pos)

/--
lemma `Integrable.measure_lt_lt_top` / 引理 `Integrable.measure_lt_lt_top`

English:
lemma Integrable.measure_lt_lt_top
  statement: {f : α -> β} [Lattice β] [HasSolidNorm β] [AddLeftMono β]
  proof: lt_of_le_of_lt (measure_mono (fun _ hx => (Set.mem_ofPred_eq ▸ hx).le))
    (Integrable.measure_le_lt_top hf c_neg)

中文:
引理 可积.measure_lt_lt_top
  结论: {f : α -> β} [格 β] [有Solid范数 β] [AddLeftMono β]
  证明: lt_of_le_of_lt (measure_mono (fun _ hx => (Set.mem_ofPred_eq ▸ hx).le))
    (Integrable.measure_le_lt_top hf c_neg)

Depends on / 依赖: Integrable, Integrable.measure_le_lt_top, Set.mem_ofPred_eq, c_neg, lt_of_le_of_lt, measure_le_lt_top, measure_mono, mem_ofPred_eq
-/
lemma Integrable.measure_lt_lt_top {f : α -> β} [Lattice β] [HasSolidNorm β] [AddLeftMono β]
    (hf : Integrable f μ) {c : β} (c_neg : c < 0) :
    μ {a : α | f a < c} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ hx => (Set.mem_ofPred_eq ▸ hx).le))
    (Integrable.measure_le_lt_top hf c_neg)

/--
theorem `LipschitzWith.integrable_comp_iff_of_antilipschitz` / 定理 `LipschitzWith.integrable_comp_iff_of_antilipschitz`

English:
theorem LipschitzWith.integrable_comp_iff_of_antilipschitz
  statement: {K K'} {f : α -> β} {g : β -> γ}
  proof: by
  simp [← memLp_one_iff_integrable, hg.memLp_comp_iff_of_antilipschitz hg' g0]

@[fun_prop]

中文:
定理 LipschitzWith.integrable_comp_iff_of_antilipschitz
  结论: {K K'} {f : α -> β} {g : β -> γ}
  证明: by
  simp [← memLp_one_iff_integrable, hg.memLp_comp_iff_of_antilipschitz hg' g0]

@[fun_prop]

Depends on / 依赖: hg.memLp_comp_iff_of_antilipschitz, memLp_comp_iff_of_antilipschitz, memLp_one_iff_integrable
-/
theorem LipschitzWith.integrable_comp_iff_of_antilipschitz {K K'} {f : α -> β} {g : β -> γ}
    (hg : LipschitzWith K g) (hg' : AntilipschitzWith K' g) (g0 : g 0 = 0) :
    Integrable (g ∘ f) μ ↔ Integrable f μ := by
  simp [← memLp_one_iff_integrable, hg.memLp_comp_iff_of_antilipschitz hg' g0]

@[fun_prop]
/--
theorem `Integrable.real_toNNReal` / 定理 `Integrable.real_toNNReal`

English:
theorem Integrable.real_toNNReal
  given: {f : α -> Real} (hf : Integrable f μ)
  proof: by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  refine lt_of_le_of_lt ?_ ((hasFiniteIntegral_iff_norm _).1 hf.hasFiniteIntegral)
  apply lintegral_mono
  intro x
  simp [abs_le, le_abs_self]

中文:
定理 可积.real_toNN实数
  条件: {f : α -> 实数} (hf : 可积 f μ)
  证明: by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  refine lt_of_le_of_lt ?_ ((hasFiniteIntegral_iff_norm _).1 hf.hasFiniteIntegral)
  apply lintegral_mono
  intro x
  simp [abs_le, le_abs_self]

Depends on / 依赖: abs_le, fun_prop, hasFiniteIntegral, hasFiniteIntegral_iff_norm, hf.hasFiniteIntegral, le_abs_self, lintegral_mono, lt_of_le_of_lt
-/
theorem Integrable.real_toNNReal {f : α -> Real} (hf : Integrable f μ) :
    Integrable (fun x => ((f x).toNNReal : Real)) μ := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  refine lt_of_le_of_lt ?_ ((hasFiniteIntegral_iff_norm _).1 hf.hasFiniteIntegral)
  apply lintegral_mono
  intro x
  simp [abs_le, le_abs_self]

/--
theorem `ofReal_toReal_ae_eq` / 定理 `ofReal_toReal_ae_eq`

English:
theorem ofReal_toReal_ae_eq
  given: {f : α -> Real>=0∞} (hf : forallᵐ x ∂μ, f x < ∞)
  proof: by
  filter_upwards [hf]
  intro x hx
  simp only [hx.ne, ofReal_toReal, Ne, not_false_iff]

中文:
定理 of实数_to实数_ae_eq
  条件: {f : α -> 实数>=0∞} (hf : 对任意ᵐ x ∂μ, f x < ∞)
  证明: by
  filter_upwards [hf]
  intro x hx
  simp only [hx.ne, ofReal_toReal, Ne, not_false_iff]

Depends on / 依赖: filter_upwards, hx.ne, not_false_iff, ofReal_toReal
-/
theorem ofReal_toReal_ae_eq {f : α -> Real>=0∞} (hf : forallᵐ x ∂μ, f x < ∞) :
    (fun x => ENNReal.ofReal (f x).toReal) =ᵐ[μ] f := by
  filter_upwards [hf]
  intro x hx
  simp only [hx.ne, ofReal_toReal, Ne, not_false_iff]

/--
theorem `coe_toNNReal_ae_eq` / 定理 `coe_toNNReal_ae_eq`

English:
theorem coe_toNNReal_ae_eq
  given: {f : α -> Real>=0∞} (hf : forallᵐ x ∂μ, f x < ∞)
  proof: by
  filter_upwards [hf]
  intro x hx
  simp only [hx.ne, Ne, not_false_iff, coe_toNNReal]

中文:
定理 coe_toNN实数_ae_eq
  条件: {f : α -> 实数>=0∞} (hf : 对任意ᵐ x ∂μ, f x < ∞)
  证明: by
  filter_upwards [hf]
  intro x hx
  simp only [hx.ne, Ne, not_false_iff, coe_toNNReal]

Depends on / 依赖: coe_toNNReal, filter_upwards, hx.ne, not_false_iff
-/
theorem coe_toNNReal_ae_eq {f : α -> Real>=0∞} (hf : forallᵐ x ∂μ, f x < ∞) :
    (fun x => ((f x).toNNReal : Real>=0∞)) =ᵐ[μ] f := by
  filter_upwards [hf]
  intro x hx
  simp only [hx.ne, Ne, not_false_iff, coe_toNNReal]

section count

variable [MeasurableSingletonClass α] {f : α -> β}

/--
lemma `integrable_count_iff` / 引理 `integrable_count_iff`

English:
lemma integrable_count_iff
  proof: by
  -- Note: this proof would be much easier if we assumed `SecondCountableTopology G`. Without
  -- this we have to justify the claim that `f` lands a.e. in a separable subset, which is true
  -- (because summable functions have countable range) but slightly tedious to check.
  rw [Integrable]; rw [hasFiniteIntegral_count_iff]; rw [and_iff_right_iff_imp]
  intro hs
  have hs' : (Function.support f).Countable := by
    simpa only [Ne, Pi.zero_apply, eq_comm, Function.support, norm_eq_zero]
      using hs.countable_support
  let : MeasurableSpace β := borel β
  have : BorelSpace β := ⟨rfl⟩
  refine aestronglyMeasurable_iff_aemeasurable_separable.mpr ⟨?_, ?_⟩
  · refine (measurable_zero.measurable_of_countable_ne ?_).aemeasurable
    simpa only [Ne, Pi.zero_apply, eq_comm, Function.support] using hs'
  · refine ⟨f '' univ, ?_, ae_of_all _ fun a => ⟨a, ⟨mem_univ _, rfl⟩⟩⟩
    suffices f '' univ subseteq (f '' f.support) union {0} from
      (((hs'.image f).union (countable_singleton 0)).mono this).isSeparable
    grind [Function.mem_support]

中文:
引理 integrable_count_iff
  证明: by
  -- Note: this proof would be much easier if we assumed `SecondCountableTopology G`. Without
  -- this we have to justify the claim that `f` lands a.e. in a separable subset, which is true
  -- (because summable functions have countable range) but slightly tedious to check.
  rw [Integrable]; rw [hasFiniteIntegral_count_iff]; rw [and_iff_right_iff_imp]
  intro hs
  have hs' : (Function.support f).Countable := by
    simpa only [Ne, Pi.zero_apply, eq_comm, Function.support, norm_eq_zero]
      using hs.countable_support
  let : MeasurableSpace β := borel β
  have : BorelSpace β := ⟨rfl⟩
  refine aestronglyMeasurable_iff_aemeasurable_separable.mpr ⟨?_, ?_⟩
  · refine (measurable_zero.measurable_of_countable_ne ?_).aemeasurable
    simpa only [Ne, Pi.zero_apply, eq_comm, Function.support] using hs'
  · refine ⟨f '' univ, ?_, ae_of_all _ fun a => ⟨a, ⟨mem_univ _, rfl⟩⟩⟩
    suffices f '' univ subseteq (f '' f.support) union {0} from
      (((hs'.image f).union (countable_singleton 0)).mono this).isSeparable
    grind [Function.mem_support]
-/
lemma integrable_count_iff :
    Integrable f Measure.count ↔ Summable (‖f ·‖) := by
  -- Note: this proof would be much easier if we assumed `SecondCountableTopology G`. Without
  -- this we have to justify the claim that `f` lands a.e. in a separable subset, which is true
  -- (because summable functions have countable range) but slightly tedious to check.
  rw [Integrable]; rw [hasFiniteIntegral_count_iff]; rw [and_iff_right_iff_imp]
  intro hs
  have hs' : (Function.support f).Countable := by
    simpa only [Ne, Pi.zero_apply, eq_comm, Function.support, norm_eq_zero]
      using hs.countable_support
  let : MeasurableSpace β := borel β
  have : BorelSpace β := ⟨rfl⟩
  refine aestronglyMeasurable_iff_aemeasurable_separable.mpr ⟨?_, ?_⟩
  · refine (measurable_zero.measurable_of_countable_ne ?_).aemeasurable
    simpa only [Ne, Pi.zero_apply, eq_comm, Function.support] using hs'
  · refine ⟨f '' univ, ?_, ae_of_all _ fun a => ⟨a, ⟨mem_univ _, rfl⟩⟩⟩
    suffices f '' univ subseteq (f '' f.support) union {0} from
      (((hs'.image f).union (countable_singleton 0)).mono this).isSeparable
    grind [Function.mem_support]

end count

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/--
theorem `integrable_withDensity_iff_integrable_coe_smul` / 定理 `integrable_withDensity_iff_integrable_coe_smul`

English:
theorem integrable_withDensity_iff_integrable_coe_smul
  statement: {f : α -> Real>=0} (hf : Measurable f)
  proof: by
  by_cases H : AEStronglyMeasurable (fun x : α => (f x : Real) • g x) μ
  · simp only [Integrable, aestronglyMeasurable_withDensity_iff hf, hasFiniteIntegral_iff_enorm, H,
      true_and]
    rw [lintegral_withDensity_eq_lintegral_mul₀' hf.coe_nnreal_ennreal.aemeasurable]
    · simp [enorm_smul]
    · simpa [aemeasurable_withDensity_ennreal_iff hf, enorm_smul] using H.enorm
  · simp only [Integrable, aestronglyMeasurable_withDensity_iff hf, H, false_and]

中文:
定理 integrable_withDensity_iff_integrable_coe_smul
  结论: {f : α -> 实数>=0} (hf : 可测 f)
  证明: by
  by_cases H : AEStronglyMeasurable (fun x : α => (f x : Real) • g x) μ
  · simp only [Integrable, aestronglyMeasurable_withDensity_iff hf, hasFiniteIntegral_iff_enorm, H,
      true_and]
    rw [lintegral_withDensity_eq_lintegral_mul₀' hf.coe_nnreal_ennreal.aemeasurable]
    · simp [enorm_smul]
    · simpa [aemeasurable_withDensity_ennreal_iff hf, enorm_smul] using H.enorm
  · simp only [Integrable, aestronglyMeasurable_withDensity_iff hf, H, false_and]

Depends on / 依赖: AEStronglyMeasurable, H.enorm, Integrable, aemeasurable, aemeasurable_withDensity_ennreal_iff, aestronglyMeasurable_withDensity_iff, coe_nnreal_ennreal, enorm_smul, false_and, hasFiniteIntegral_iff_enorm, hf.coe_nnreal_ennreal.aemeasurable, true_and
-/
theorem integrable_withDensity_iff_integrable_coe_smul {f : α -> Real>=0} (hf : Measurable f)
    {g : α -> E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => (f x : Real) • g x) μ := by
  by_cases H : AEStronglyMeasurable (fun x : α => (f x : Real) • g x) μ
  · simp only [Integrable, aestronglyMeasurable_withDensity_iff hf, hasFiniteIntegral_iff_enorm, H,
      true_and]
    rw [lintegral_withDensity_eq_lintegral_mul₀' hf.coe_nnreal_ennreal.aemeasurable]
    · simp [enorm_smul]
    · simpa [aemeasurable_withDensity_ennreal_iff hf, enorm_smul] using H.enorm
  · simp only [Integrable, aestronglyMeasurable_withDensity_iff hf, H, false_and]

/--
theorem `integrable_withDensity_iff_integrable_smul` / 定理 `integrable_withDensity_iff_integrable_smul`

English:
theorem integrable_withDensity_iff_integrable_smul
  given: {f : α -> Real>=0} (hf : Measurable f) {g : α -> E}
  proof: integrable_withDensity_iff_integrable_coe_smul hf

中文:
定理 integrable_withDensity_iff_integrable_smul
  条件: {f : α -> 实数>=0} (hf : 可测 f) {g : α -> E}
  证明: integrable_withDensity_iff_integrable_coe_smul hf

Depends on / 依赖: integrable_withDensity_iff_integrable_coe_smul
-/
theorem integrable_withDensity_iff_integrable_smul {f : α -> Real>=0} (hf : Measurable f) {g : α -> E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => f x • g x) μ :=
  integrable_withDensity_iff_integrable_coe_smul hf

/--
theorem `integrable_withDensity_iff_integrable_smul'` / 定理 `integrable_withDensity_iff_integrable_smul'`

English:
theorem integrable_withDensity_iff_integrable_smul'
  statement: {f : α -> Real>=0∞} (hf : Measurable f)
  proof: by
  rw [← withDensity_congr_ae (coe_toNNReal_ae_eq hflt)]; rw [integrable_withDensity_iff_integrable_smul]
  · simp_rw [NNReal.smul_def, ENNReal.toReal]
  · exact hf.ennreal_toNNReal

中文:
定理 integrable_withDensity_iff_integrable_smul'
  结论: {f : α -> 实数>=0∞} (hf : 可测 f)
  证明: by
  rw [← withDensity_congr_ae (coe_toNNReal_ae_eq hflt)]; rw [integrable_withDensity_iff_integrable_smul]
  · simp_rw [NNReal.smul_def, ENNReal.toReal]
  · exact hf.ennreal_toNNReal

Depends on / 依赖: ENNReal, ENNReal.toReal, NNReal, NNReal.smul_def, coe_toNNReal_ae_eq, ennreal_toNNReal, hf.ennreal_toNNReal, integrable_withDensity_iff_integrable_smul, simp_rw, smul_def, toReal, withDensity_congr_ae
-/
theorem integrable_withDensity_iff_integrable_smul' {f : α -> Real>=0∞} (hf : Measurable f)
    (hflt : forallᵐ x ∂μ, f x < ∞) {g : α -> E} :
    Integrable g (μ.withDensity f) ↔ Integrable (fun x => (f x).toReal • g x) μ := by
  rw [← withDensity_congr_ae (coe_toNNReal_ae_eq hflt)]; rw [integrable_withDensity_iff_integrable_smul]
  · simp_rw [NNReal.smul_def, ENNReal.toReal]
  · exact hf.ennreal_toNNReal

/--
theorem `integrable_withDensity_iff_integrable_coe_smul₀` / 定理 `integrable_withDensity_iff_integrable_coe_smul₀`

English:
theorem integrable_withDensity_iff_integrable_coe_smul₀
  statement: {f : α -> Real>=0} (hf : AEMeasurable f μ)
  proof: calc
    Integrable g (μ.withDensity fun x => f x) ↔
        Integrable g (μ.withDensity fun x => (hf.mk f x : Real>=0)) := by
      suffices (fun x => (f x : Real>=0∞)) =ᵐ[μ] (fun x => (hf.mk f x : Real>=0)) by
        rw [withDensity_congr_ae this]
      filter_upwards [hf.ae_eq_mk] with x hx
      simp [hx]
    _ ↔ Integrable (fun x => ((hf.mk f x : Real>=0) : Real) • g x) μ :=
      integrable_withDensity_iff_integrable_coe_smul hf.measurable_mk
    _ ↔ Integrable (fun x => (f x : Real) • g x) μ := by
      apply integrable_congr
      filter_upwards [hf.ae_eq_mk] with x hx
      simp [hx]

中文:
定理 integrable_withDensity_iff_integrable_coe_smul₀
  结论: {f : α -> 实数>=0} (hf : 几乎处处可测 f μ)
  证明: calc
    Integrable g (μ.withDensity fun x => f x) ↔
        Integrable g (μ.withDensity fun x => (hf.mk f x : Real>=0)) := by
      suffices (fun x => (f x : Real>=0∞)) =ᵐ[μ] (fun x => (hf.mk f x : Real>=0)) by
        rw [withDensity_congr_ae this]
      filter_upwards [hf.ae_eq_mk] with x hx
      simp [hx]
    _ ↔ Integrable (fun x => ((hf.mk f x : Real>=0) : Real) • g x) μ :=
      integrable_withDensity_iff_integrable_coe_smul hf.measurable_mk
    _ ↔ Integrable (fun x => (f x : Real) • g x) μ := by
      apply integrable_congr
      filter_upwards [hf.ae_eq_mk] with x hx
      simp [hx]

Depends on / 依赖: Integrable, ae_eq_mk, filter_upwards, hf.ae_eq_mk, hf.measurable_mk, hf.mk, integrable_congr, integrable_withDensity_iff_integrable_coe_smul, measurable_mk, withDensity, withDensity_congr_ae
-/
theorem integrable_withDensity_iff_integrable_coe_smul₀ {f : α -> Real>=0} (hf : AEMeasurable f μ)
    {g : α -> E} :
    Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => (f x : Real) • g x) μ :=
  calc
    Integrable g (μ.withDensity fun x => f x) ↔
        Integrable g (μ.withDensity fun x => (hf.mk f x : Real>=0)) := by
      suffices (fun x => (f x : Real>=0∞)) =ᵐ[μ] (fun x => (hf.mk f x : Real>=0)) by
        rw [withDensity_congr_ae this]
      filter_upwards [hf.ae_eq_mk] with x hx
      simp [hx]
    _ ↔ Integrable (fun x => ((hf.mk f x : Real>=0) : Real) • g x) μ :=
      integrable_withDensity_iff_integrable_coe_smul hf.measurable_mk
    _ ↔ Integrable (fun x => (f x : Real) • g x) μ := by
      apply integrable_congr
      filter_upwards [hf.ae_eq_mk] with x hx
      simp [hx]

/--
theorem `integrable_withDensity_iff_integrable_smul₀'` / 定理 `integrable_withDensity_iff_integrable_smul₀'`

English:
theorem integrable_withDensity_iff_integrable_smul₀'
  statement: {f : α -> Real>=0∞} (hf : AEMeasurable f μ)
  proof: by
  rw [← withDensity_congr_ae (coe_toNNReal_ae_eq hflt)]; rw [integrable_withDensity_iff_integrable_coe_smul₀]
  · congr!
  · exact hf.ennreal_toNNReal

中文:
定理 integrable_withDensity_iff_integrable_smul₀'
  结论: {f : α -> 实数>=0∞} (hf : 几乎处处可测 f μ)
  证明: by
  rw [← withDensity_congr_ae (coe_toNNReal_ae_eq hflt)]; rw [integrable_withDensity_iff_integrable_coe_smul₀]
  · congr!
  · exact hf.ennreal_toNNReal

Depends on / 依赖: coe_toNNReal_ae_eq, ennreal_toNNReal, hf.ennreal_toNNReal, withDensity_congr_ae
-/
theorem integrable_withDensity_iff_integrable_smul₀' {f : α -> Real>=0∞} (hf : AEMeasurable f μ)
    (hflt : forallᵐ x ∂μ, f x < ∞) {g : α -> E} :
    Integrable g (μ.withDensity f) ↔ Integrable (fun x => (f x).toReal • g x) μ := by
  rw [← withDensity_congr_ae (coe_toNNReal_ae_eq hflt)]; rw [integrable_withDensity_iff_integrable_coe_smul₀]
  · congr!
  · exact hf.ennreal_toNNReal

/--
theorem `integrable_withDensity_iff_integrable_smul₀` / 定理 `integrable_withDensity_iff_integrable_smul₀`

English:
theorem integrable_withDensity_iff_integrable_smul₀
  statement: {f : α -> Real>=0} (hf : AEMeasurable f μ)
  proof: integrable_withDensity_iff_integrable_coe_smul₀ hf

中文:
定理 integrable_withDensity_iff_integrable_smul₀
  结论: {f : α -> 实数>=0} (hf : 几乎处处可测 f μ)
  证明: integrable_withDensity_iff_integrable_coe_smul₀ hf
-/
theorem integrable_withDensity_iff_integrable_smul₀ {f : α -> Real>=0} (hf : AEMeasurable f μ)
    {g : α -> E} : Integrable g (μ.withDensity fun x => f x) ↔ Integrable (fun x => f x • g x) μ :=
  integrable_withDensity_iff_integrable_coe_smul₀ hf

end

/--
theorem `integrable_withDensity_iff` / 定理 `integrable_withDensity_iff`

English:
theorem integrable_withDensity_iff
  statement: {f : α -> Real>=0∞} (hf : Measurable f) (hflt : forallᵐ x ∂μ, f x < ∞)
  proof: by
  have : (fun x => g x * (f x).toReal) = fun x => (f x).toReal • g x := by simp [mul_comm]
  rw [this]
  exact integrable_withDensity_iff_integrable_smul' hf hflt

中文:
定理 integrable_withDensity_iff
  结论: {f : α -> 实数>=0∞} (hf : 可测 f) (hflt : 对任意ᵐ x ∂μ, f x < ∞)
  证明: by
  have : (fun x => g x * (f x).toReal) = fun x => (f x).toReal • g x := by simp [mul_comm]
  rw [this]
  exact integrable_withDensity_iff_integrable_smul' hf hflt

Depends on / 依赖: integrable_withDensity_iff_integrable_smul, mul_comm, toReal
-/
theorem integrable_withDensity_iff {f : α -> Real>=0∞} (hf : Measurable f) (hflt : forallᵐ x ∂μ, f x < ∞)
    {g : α -> Real} : Integrable g (μ.withDensity f) ↔ Integrable (fun x => g x * (f x).toReal) μ := by
  have : (fun x => g x * (f x).toReal) = fun x => (f x).toReal • g x := by simp [mul_comm]
  rw [this]
  exact integrable_withDensity_iff_integrable_smul' hf hflt

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/--
theorem `memL1_smul_of_L1_withDensity` / 定理 `memL1_smul_of_L1_withDensity`

English:
theorem memL1_smul_of_L1_withDensity
  statement: {f : α -> Real>=0} (f_meas : Measurable f)
  proof: memLp_one_iff_integrable.2
(integrable_withDensity_iff_integrable_smul f_meas).1 memLp_one_iff_integrable.1 (Lp.memLp u)

中文:
定理 memL1_smul_of_L1_withDensity
  结论: {f : α -> 实数>=0} (f_meas : 可测 f)
  证明: memLp_one_iff_integrable.2
(integrable_withDensity_iff_integrable_smul f_meas).1 memLp_one_iff_integrable.1 (Lp.memLp u)

Depends on / 依赖: Lp.memLp, f_meas, integrable_withDensity_iff_integrable_smul, memLp_one_iff_integrable
-/
theorem memL1_smul_of_L1_withDensity {f : α -> Real>=0} (f_meas : Measurable f)
    (u : Lp E 1 (μ.withDensity fun x => f x)) : MemLp (fun x => f x • u x) 1 μ :=
memLp_one_iff_integrable.2
(integrable_withDensity_iff_integrable_smul f_meas).1 memLp_one_iff_integrable.1 (Lp.memLp u)

variable (μ)

/--
Definition of `withDensitySMulLI` / `withDensitySMulLI` 的定义

English:
definition withDensitySMulLI
  signature: {f : α -> Real>=0} (f_meas : Measurable f)
  body: (memL1_smul_of_L1_withDensity f_meas u).toLp _
  map_add' := by
    intro u v
    ext1
    filter_upwards [(memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp,
      (memL1_smul_of_L1_withDensity f_meas v).coeFn_toLp,
      (memL1_smul_of_L1_withDensity f_meas (u + v)).coeFn_toLp,
      Lp.coeFn_add ((memL1_smul_of_L1_withDensity f_meas u).toLp _)
        ((memL1_smul_of_L1_withDensity f_meas v).toLp _),
      (ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 (Lp.coeFn_add u v)]
    intro x hu hv huv h' h''
    rw [huv]; rw [h']; rw [Pi.add_apply]; rw [hu]; rw [hv]
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, add_zero]
    · rw [h'' _, Pi.add_apply, smul_add]
      simpa only [Ne, ENNReal.coe_eq_zero] using hx
  map_smul' := by
    intro r u
    ext1
    filter_upwards [(ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 (Lp.coeFn_smul r u),
      (memL1_smul_of_L1_withDensity f_meas (r • u)).coeFn_toLp,
      Lp.coeFn_smul r ((memL1_smul_of_L1_withDensity f_meas u).toLp _),
      (memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp]
    intro x h h' h'' h'''
    rw [RingHom.id_apply]; rw [h']; rw [h'']; rw [Pi.smul_apply]; rw [h''']
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, smul_zero]
    · rw [h _, smul_comm, Pi.smul_apply]
      simpa only [Ne, ENNReal.coe_eq_zero] using hx
  norm_map' := by
    intro u
    simp only [eLpNorm, LinearMap.coe_mk, AddHom.coe_mk,
      one_ne_zero, ENNReal.one_ne_top, ENNReal.toReal_one, if_false, eLpNorm', ENNReal.rpow_one,
      _root_.div_one, Lp.norm_def]
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ f_meas.coe_nnreal_ennreal
        (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top)]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [(memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp] with x hx
    rw [hx]
    simp [NNReal.smul_def, enorm_smul]

@[simp]

中文:
定义 withDensitySMulLI
  签名: {f : α -> 实数>=0} (f_meas : 可测 f)
  定义体: (memL1_smul_of_L1_withDensity f_meas u).toLp _
  map_add' := by
    intro u v
    ext1
    filter_upwards [(memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp,
      (memL1_smul_of_L1_withDensity f_meas v).coeFn_toLp,
      (memL1_smul_of_L1_withDensity f_meas (u + v)).coeFn_toLp,
      Lp.coeFn_add ((memL1_smul_of_L1_withDensity f_meas u).toLp _)
        ((memL1_smul_of_L1_withDensity f_meas v).toLp _),
      (ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 (Lp.coeFn_add u v)]
    intro x hu hv huv h' h''
    rw [huv]; rw [h']; rw [Pi.add_apply]; rw [hu]; rw [hv]
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, add_zero]
    · rw [h'' _, Pi.add_apply, smul_add]
      simpa only [Ne, ENNReal.coe_eq_zero] using hx
  map_smul' := by
    intro r u
    ext1
    filter_upwards [(ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 (Lp.coeFn_smul r u),
      (memL1_smul_of_L1_withDensity f_meas (r • u)).coeFn_toLp,
      Lp.coeFn_smul r ((memL1_smul_of_L1_withDensity f_meas u).toLp _),
      (memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp]
    intro x h h' h'' h'''
    rw [RingHom.id_apply]; rw [h']; rw [h'']; rw [Pi.smul_apply]; rw [h''']
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, smul_zero]
    · rw [h _, smul_comm, Pi.smul_apply]
      simpa only [Ne, ENNReal.coe_eq_zero] using hx
  norm_map' := by
    intro u
    simp only [eLpNorm, LinearMap.coe_mk, AddHom.coe_mk,
      one_ne_zero, ENNReal.one_ne_top, ENNReal.toReal_one, if_false, eLpNorm', ENNReal.rpow_one,
      _root_.div_one, Lp.norm_def]
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ f_meas.coe_nnreal_ennreal
        (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top)]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [(memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp] with x hx
    rw [hx]
    simp [NNReal.smul_def, enorm_smul]

@[simp]

Depends on / 依赖: f_meas, memL1_smul_of_L1_withDensity
-/
noncomputable def withDensitySMulLI {f : α -> Real>=0} (f_meas : Measurable f) :
    Lp E 1 (μ.withDensity fun x => f x) ->ₗᵢ[Real] Lp E 1 μ where
  toFun u := (memL1_smul_of_L1_withDensity f_meas u).toLp _
  map_add' := by
    intro u v
    ext1
    filter_upwards [(memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp,
      (memL1_smul_of_L1_withDensity f_meas v).coeFn_toLp,
      (memL1_smul_of_L1_withDensity f_meas (u + v)).coeFn_toLp,
      Lp.coeFn_add ((memL1_smul_of_L1_withDensity f_meas u).toLp _)
        ((memL1_smul_of_L1_withDensity f_meas v).toLp _),
      (ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 (Lp.coeFn_add u v)]
    intro x hu hv huv h' h''
    rw [huv]; rw [h']; rw [Pi.add_apply]; rw [hu]; rw [hv]
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, add_zero]
    · rw [h'' _, Pi.add_apply, smul_add]
      simpa only [Ne, ENNReal.coe_eq_zero] using hx
  map_smul' := by
    intro r u
    ext1
    filter_upwards [(ae_withDensity_iff f_meas.coe_nnreal_ennreal).1 (Lp.coeFn_smul r u),
      (memL1_smul_of_L1_withDensity f_meas (r • u)).coeFn_toLp,
      Lp.coeFn_smul r ((memL1_smul_of_L1_withDensity f_meas u).toLp _),
      (memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp]
    intro x h h' h'' h'''
    rw [RingHom.id_apply]; rw [h']; rw [h'']; rw [Pi.smul_apply]; rw [h''']
    rcases eq_or_ne (f x) 0 with (hx | hx)
    · simp only [hx, zero_smul, smul_zero]
    · rw [h _, smul_comm, Pi.smul_apply]
      simpa only [Ne, ENNReal.coe_eq_zero] using hx
  norm_map' := by
    intro u
    simp only [eLpNorm, LinearMap.coe_mk, AddHom.coe_mk,
      one_ne_zero, ENNReal.one_ne_top, ENNReal.toReal_one, if_false, eLpNorm', ENNReal.rpow_one,
      _root_.div_one, Lp.norm_def]
    rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ f_meas.coe_nnreal_ennreal
        (Filter.Eventually.of_forall fun x => ENNReal.coe_lt_top)]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [(memL1_smul_of_L1_withDensity f_meas u).coeFn_toLp] with x hx
    rw [hx]
    simp [NNReal.smul_def, enorm_smul]

@[simp]
/--
theorem `withDensitySMulLI_apply` / 定理 `withDensitySMulLI_apply`

English:
theorem withDensitySMulLI_apply
  statement: {f : α -> Real>=0} (f_meas : Measurable f)
  proof: rfl

中文:
定理 withDensitySMulLI_apply
  结论: {f : α -> 实数>=0} (f_meas : 可测 f)
  证明: rfl

Depends on / 依赖: f_meas
-/
theorem withDensitySMulLI_apply {f : α -> Real>=0} (f_meas : Measurable f)
    (u : Lp E 1 (μ.withDensity fun x => f x)) :
    withDensitySMulLI μ (E := E) f_meas u =
      (memL1_smul_of_L1_withDensity f_meas u).toLp fun x => f x • u x :=
  rfl

end

section ENNReal

/--
theorem `mem_L1_toReal_of_lintegral_ne_top` / 定理 `mem_L1_toReal_of_lintegral_ne_top`

English:
theorem mem_L1_toReal_of_lintegral_ne_top
  statement: {f : α -> Real>=0∞} (hfm : AEMeasurable f μ)
  proof: by
  rw [MemLp]; rw [eLpNorm_one_eq_lintegral_enorm]
  exact ⟨(AEMeasurable.ennreal_toReal hfm).aestronglyMeasurable,
    hasFiniteIntegral_toReal_of_lintegral_ne_top hfi⟩

中文:
定理 mem_L1_to实数_of_lintegral_ne_top
  结论: {f : α -> 实数>=0∞} (hfm : 几乎处处可测 f μ)
  证明: by
  rw [MemLp]; rw [eLpNorm_one_eq_lintegral_enorm]
  exact ⟨(AEMeasurable.ennreal_toReal hfm).aestronglyMeasurable,
    hasFiniteIntegral_toReal_of_lintegral_ne_top hfi⟩

Depends on / 依赖: AEMeasurable, AEMeasurable.ennreal_toReal, aestronglyMeasurable, eLpNorm_one_eq_lintegral_enorm, ennreal_toReal, hasFiniteIntegral_toReal_of_lintegral_ne_top
-/
theorem mem_L1_toReal_of_lintegral_ne_top {f : α -> Real>=0∞} (hfm : AEMeasurable f μ)
    (hfi : ∫⁻ x, f x ∂μ != ∞) : MemLp (fun x => (f x).toReal) 1 μ := by
  rw [MemLp]; rw [eLpNorm_one_eq_lintegral_enorm]
  exact ⟨(AEMeasurable.ennreal_toReal hfm).aestronglyMeasurable,
    hasFiniteIntegral_toReal_of_lintegral_ne_top hfi⟩

/--
theorem `integrable_toReal_of_lintegral_ne_top` / 定理 `integrable_toReal_of_lintegral_ne_top`

English:
theorem integrable_toReal_of_lintegral_ne_top
  statement: {f : α -> Real>=0∞} (hfm : AEMeasurable f μ)
  proof: memLp_one_iff_integrable.1 mem_L1_toReal_of_lintegral_ne_top hfm hfi

中文:
定理 integrable_to实数_of_lintegral_ne_top
  结论: {f : α -> 实数>=0∞} (hfm : 几乎处处可测 f μ)
  证明: memLp_one_iff_integrable.1 mem_L1_toReal_of_lintegral_ne_top hfm hfi

Depends on / 依赖: memLp_one_iff_integrable, mem_L1_toReal_of_lintegral_ne_top
-/
theorem integrable_toReal_of_lintegral_ne_top {f : α -> Real>=0∞} (hfm : AEMeasurable f μ)
    (hfi : ∫⁻ x, f x ∂μ != ∞) : Integrable (fun x => (f x).toReal) μ :=
memLp_one_iff_integrable.1 mem_L1_toReal_of_lintegral_ne_top hfm hfi

/--
lemma `integrable_toReal_iff` / 引理 `integrable_toReal_iff`

English:
lemma integrable_toReal_iff
  given: {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hf_ne_top : forallᵐ x ∂μ, f x != ∞)
  proof: by
  rw [Integrable]; rw [hasFiniteIntegral_toReal_iff hf_ne_top]
  simp only [hf.ennreal_toReal.aestronglyMeasurable, ne_eq, true_and]

中文:
引理 integrable_to实数_iff
  条件: {f : α -> 实数>=0∞} (hf : 几乎处处可测 f μ) (hf_ne_top : 对任意ᵐ x ∂μ, f x != ∞)
  证明: by
  rw [Integrable]; rw [hasFiniteIntegral_toReal_iff hf_ne_top]
  simp only [hf.ennreal_toReal.aestronglyMeasurable, ne_eq, true_and]

Depends on / 依赖: Integrable, aestronglyMeasurable, ennreal_toReal, hasFiniteIntegral_toReal_iff, hf.ennreal_toReal.aestronglyMeasurable, hf_ne_top, ne_eq, true_and
-/
lemma integrable_toReal_iff {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (hf_ne_top : forallᵐ x ∂μ, f x != ∞) :
    Integrable (fun x => (f x).toReal) μ ↔ ∫⁻ x, f x ∂μ != ∞ := by
  rw [Integrable]; rw [hasFiniteIntegral_toReal_iff hf_ne_top]
  simp only [hf.ennreal_toReal.aestronglyMeasurable, ne_eq, true_and]

/--
lemma `lintegral_ofReal_ne_top_iff_integrable` / 引理 `lintegral_ofReal_ne_top_iff_integrable`

English:
lemma lintegral_ofReal_ne_top_iff_integrable
  statement: {f : α -> Real}
  proof: by
  rw [Integrable]; rw [hasFiniteIntegral_iff_ofReal hf]
  simp [hfm]

中文:
引理 lintegral_of实数_ne_top_iff_integrable
  结论: {f : α -> 实数}
  证明: by
  rw [Integrable]; rw [hasFiniteIntegral_iff_ofReal hf]
  simp [hfm]

Depends on / 依赖: Integrable, hasFiniteIntegral_iff_ofReal
-/
lemma lintegral_ofReal_ne_top_iff_integrable {f : α -> Real}
    (hfm : AEStronglyMeasurable f μ) (hf : 0 <=ᵐ[μ] f) :
    ∫⁻ a, ENNReal.ofReal (f a) ∂μ != ∞ ↔ Integrable f μ := by
  rw [Integrable]; rw [hasFiniteIntegral_iff_ofReal hf]
  simp [hfm]

end ENNReal

section PosPart

/-! ### Lemmas used for defining the positive part of an `L¹` function -/


@[fun_prop]
/--
theorem `Integrable.pos_part` / 定理 `Integrable.pos_part`

English:
theorem Integrable.pos_part
  given: {f : α -> Real} (hf : Integrable f μ)
  proof: by
  constructor <;> fun_prop

@[fun_prop]

中文:
定理 可积.pos_part
  条件: {f : α -> 实数} (hf : 可积 f μ)
  证明: by
  constructor <;> fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop
-/
theorem Integrable.pos_part {f : α -> Real} (hf : Integrable f μ) :
    Integrable (fun a => max (f a) 0) μ := by
  constructor <;> fun_prop

@[fun_prop]
/--
theorem `Integrable.neg_part` / 定理 `Integrable.neg_part`

English:
theorem Integrable.neg_part
  given: {f : α -> Real} (hf : Integrable f μ)
  proof: hf.neg.pos_part

中文:
定理 可积.neg_part
  条件: {f : α -> 实数} (hf : 可积 f μ)
  证明: hf.neg.pos_part

Depends on / 依赖: hf.neg.pos_part, pos_part
-/
theorem Integrable.neg_part {f : α -> Real} (hf : Integrable f μ) :
    Integrable (fun a => max (-f a) 0) μ :=
  hf.neg.pos_part

end PosPart

section IsBoundedSMul

variable {𝕜 : Type*}
  {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

@[to_fun (attr := fun_prop)]
/--
theorem `Integrable.smul` / 定理 `Integrable.smul`

English:
theorem Integrable.smul
  statement: [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 β] [IsBoundedSMul 𝕜 β] (c : 𝕜)
  proof: by
  constructor <;> fun_prop

@[to_fun (attr := fun_prop)]

中文:
定理 可积.smul
  结论: [赋范交换加群 𝕜] [SMulZero类 𝕜 β] [是BoundedSMul 𝕜 β] (c : 𝕜)
  证明: by
  constructor <;> fun_prop

@[to_fun (attr := fun_prop)]
-/
theorem Integrable.smul [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 β] [IsBoundedSMul 𝕜 β] (c : 𝕜)
    {f : α -> β} (hf : Integrable f μ) : Integrable (c • f) μ := by
  constructor <;> fun_prop

@[to_fun (attr := fun_prop)]
/--
theorem `Integrable.smul_enorm` / 定理 `Integrable.smul_enorm`

English:
theorem Integrable.smul_enorm
  proof: by
  constructor <;> fun_prop

中文:
定理 可积.smul_enorm
  证明: by
  constructor <;> fun_prop

Depends on / 依赖: fun_prop
-/
theorem Integrable.smul_enorm
    [NormedAddCommGroup 𝕜] [SMul 𝕜 ε] [ContinuousConstSMul 𝕜 ε] [ENormSMulClass 𝕜 ε] (c : 𝕜)
    {f : α -> ε} (hf : Integrable f μ) : Integrable (c • f) μ := by
  constructor <;> fun_prop

/--
theorem `_root_.IsUnit.integrable_smul_iff` / 定理 `_root_.IsUnit.integrable_smul_iff`

English:
theorem _root_.IsUnit.integrable_smul_iff
  statement: [NormedRing 𝕜] [MulActionWithZero 𝕜 β]
  proof: and_congr hc.aestronglyMeasurable_const_smul_iff (hasFiniteIntegral_smul_iff hc f)

中文:
定理 _root_.是单位.integrable_smul_iff
  结论: [赋范环 𝕜] [带零乘法作用 𝕜 β]
  证明: and_congr hc.aestronglyMeasurable_const_smul_iff (hasFiniteIntegral_smul_iff hc f)

Depends on / 依赖: aestronglyMeasurable_const_smul_iff, and_congr, hasFiniteIntegral_smul_iff, hc.aestronglyMeasurable_const_smul_iff
-/
theorem _root_.IsUnit.integrable_smul_iff [NormedRing 𝕜] [MulActionWithZero 𝕜 β]
    [IsBoundedSMul 𝕜 β] {c : 𝕜} (hc : IsUnit c) (f : α -> β) :
    Integrable (c • f) μ ↔ Integrable f μ :=
  and_congr hc.aestronglyMeasurable_const_smul_iff (hasFiniteIntegral_smul_iff hc f)

/--
theorem `integrable_smul_iff` / 定理 `integrable_smul_iff`

English:
theorem integrable_smul_iff
  statement: [NormedDivisionRing 𝕜] [MulActionWithZero 𝕜 β]
  proof: (IsUnit.mk0 _ hc).integrable_smul_iff f

中文:
定理 integrable_smul_iff
  结论: [NormedDivision环 𝕜] [带零乘法作用 𝕜 β]
  证明: (IsUnit.mk0 _ hc).integrable_smul_iff f

Depends on / 依赖: IsUnit, IsUnit.mk0, integrable_smul_iff
-/
theorem integrable_smul_iff [NormedDivisionRing 𝕜] [MulActionWithZero 𝕜 β]
    [IsBoundedSMul 𝕜 β] {c : 𝕜} (hc : c != 0) (f : α -> β) :
    Integrable (c • f) μ ↔ Integrable f μ :=
  (IsUnit.mk0 _ hc).integrable_smul_iff f

/--
theorem `integrable_fun_smul_iff` / 定理 `integrable_fun_smul_iff`

English:
theorem integrable_fun_smul_iff
  statement: [NormedDivisionRing 𝕜] [MulActionWithZero 𝕜 β] [IsBoundedSMul 𝕜 β]
  proof: integrable_smul_iff hc f

中文:
定理 integrable_fun_smul_iff
  结论: [NormedDivision环 𝕜] [带零乘法作用 𝕜 β] [是BoundedSMul 𝕜 β]
  证明: integrable_smul_iff hc f

Depends on / 依赖: integrable_smul_iff
-/
theorem integrable_fun_smul_iff [NormedDivisionRing 𝕜] [MulActionWithZero 𝕜 β] [IsBoundedSMul 𝕜 β]
    {c : 𝕜} (hc : c != 0) (f : α -> β) :
    Integrable (fun x => c • f x) μ ↔ Integrable f μ :=
  integrable_smul_iff hc f

variable [NormedRing 𝕜] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]

/--
theorem `Integrable.smul_of_top_right` / 定理 `Integrable.smul_of_top_right`

English:
theorem Integrable.smul_of_top_right
  statement: {f : α -> β} {φ : α -> 𝕜} (hf : Integrable f μ)
  proof: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact MemLp.smul hf hφ

中文:
定理 可积.smul_of_top_right
  结论: {f : α -> β} {φ : α -> 𝕜} (hf : 可积 f μ)
  证明: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact MemLp.smul hf hφ

Depends on / 依赖: MemLp.smul, memLp_one_iff_integrable
-/
theorem Integrable.smul_of_top_right {f : α -> β} {φ : α -> 𝕜} (hf : Integrable f μ)
    (hφ : MemLp φ ∞ μ) : Integrable (φ • f) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact MemLp.smul hf hφ

/--
theorem `Integrable.bdd_smul` / 定理 `Integrable.bdd_smul`

English:
theorem Integrable.bdd_smul
  statement: {f : α -> β} {φ : α -> 𝕜} (hf : Integrable f μ)
  proof: hf.smul_of_top_right (memLp_top_of_bound hφ1 C hφ2)

中文:
定理 可积.bdd_smul
  结论: {f : α -> β} {φ : α -> 𝕜} (hf : 可积 f μ)
  证明: hf.smul_of_top_right (memLp_top_of_bound hφ1 C hφ2)

Depends on / 依赖: hf.smul_of_top_right, memLp_top_of_bound, smul_of_top_right
-/
theorem Integrable.bdd_smul {f : α -> β} {φ : α -> 𝕜} (hf : Integrable f μ)
    (C : Real) (hφ1 : AEStronglyMeasurable φ μ) (hφ2 : forallᵐ a ∂μ, ‖φ a‖ <= C) :
    Integrable (φ • f) μ :=
  hf.smul_of_top_right (memLp_top_of_bound hφ1 C hφ2)

/--
theorem `Integrable.smul_of_top_left` / 定理 `Integrable.smul_of_top_left`

English:
theorem Integrable.smul_of_top_left
  statement: {f : α -> β} {φ : α -> 𝕜} (hφ : Integrable φ μ)
  proof: by
  rw [← memLp_one_iff_integrable] at hφ ⊢
  exact MemLp.smul hf hφ

中文:
定理 可积.smul_of_top_left
  结论: {f : α -> β} {φ : α -> 𝕜} (hφ : 可积 φ μ)
  证明: by
  rw [← memLp_one_iff_integrable] at hφ ⊢
  exact MemLp.smul hf hφ

Depends on / 依赖: MemLp.smul, memLp_one_iff_integrable
-/
theorem Integrable.smul_of_top_left {f : α -> β} {φ : α -> 𝕜} (hφ : Integrable φ μ)
    (hf : MemLp f ∞ μ) : Integrable (φ • f) μ := by
  rw [← memLp_one_iff_integrable] at hφ ⊢
  exact MemLp.smul hf hφ

/--
theorem `Integrable.smul_bdd` / 定理 `Integrable.smul_bdd`

English:
theorem Integrable.smul_bdd
  statement: {f : α -> β} {φ : α -> 𝕜} (hφ : Integrable φ μ)
  proof: hφ.smul_of_top_left (memLp_top_of_bound hf1 C hf2)

@[fun_prop]

中文:
定理 可积.smul_bdd
  结论: {f : α -> β} {φ : α -> 𝕜} (hφ : 可积 φ μ)
  证明: hφ.smul_of_top_left (memLp_top_of_bound hf1 C hf2)

@[fun_prop]

Depends on / 依赖: memLp_top_of_bound, smul_of_top_left
-/
theorem Integrable.smul_bdd {f : α -> β} {φ : α -> 𝕜} (hφ : Integrable φ μ)
    (C : Real) (hf1 : AEStronglyMeasurable f μ) (hf2 : forallᵐ a ∂μ, ‖f a‖ <= C) :
    Integrable (φ • f) μ :=
  hφ.smul_of_top_left (memLp_top_of_bound hf1 C hf2)

@[fun_prop]
/--
theorem `Integrable.smul_const` / 定理 `Integrable.smul_const`

English:
theorem Integrable.smul_const
  given: {f : α -> 𝕜} (hf : Integrable f μ) (c : β)
  proof: hf.smul_of_top_left (memLp_top_const c)

中文:
定理 可积.smul_const
  条件: {f : α -> 𝕜} (hf : 可积 f μ) (c : β)
  证明: hf.smul_of_top_left (memLp_top_const c)

Depends on / 依赖: hf.smul_of_top_left, memLp_top_const, smul_of_top_left
-/
theorem Integrable.smul_const {f : α -> 𝕜} (hf : Integrable f μ) (c : β) :
    Integrable (fun x => f x • c) μ :=
  hf.smul_of_top_left (memLp_top_const c)

end IsBoundedSMul

section NormedSpaceOverCompleteField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
theorem `integrable_smul_const` / 定理 `integrable_smul_const`

English:
theorem integrable_smul_const
  given: {f : α -> 𝕜} {c : E} (hc : c != 0)
  proof: by
  simp_rw [Integrable, aestronglyMeasurable_smul_const_iff (f := f) hc, and_congr_right_iff,
    hasFiniteIntegral_iff_enorm, enorm_smul]
  intro _; rw [lintegral_mul_const' _ _ enorm_ne_top, ENNReal.mul_lt_top_iff]
  have : forall x : Real>=0∞, x = 0 -> x < ∞ := by simp
  simp [hc, or_iff_left_of_imp (this _)]

中文:
定理 integrable_smul_const
  条件: {f : α -> 𝕜} {c : E} (hc : c != 0)
  证明: by
  simp_rw [Integrable, aestronglyMeasurable_smul_const_iff (f := f) hc, and_congr_right_iff,
    hasFiniteIntegral_iff_enorm, enorm_smul]
  intro _; rw [lintegral_mul_const' _ _ enorm_ne_top, ENNReal.mul_lt_top_iff]
  have : forall x : Real>=0∞, x = 0 -> x < ∞ := by simp
  simp [hc, or_iff_left_of_imp (this _)]

Depends on / 依赖: ENNReal, ENNReal.mul_lt_top_iff, Integrable, aestronglyMeasurable_smul_const_iff, and_congr_right_iff, enorm_ne_top, enorm_smul, hasFiniteIntegral_iff_enorm, lintegral_mul_const, mul_lt_top_iff, or_iff_left_of_imp, simp_rw
-/
theorem integrable_smul_const {f : α -> 𝕜} {c : E} (hc : c != 0) :
    Integrable (fun x => f x • c) μ ↔ Integrable f μ := by
  simp_rw [Integrable, aestronglyMeasurable_smul_const_iff (f := f) hc, and_congr_right_iff,
    hasFiniteIntegral_iff_enorm, enorm_smul]
  intro _; rw [lintegral_mul_const' _ _ enorm_ne_top, ENNReal.mul_lt_top_iff]
  have : forall x : Real>=0∞, x = 0 -> x < ∞ := by simp
  simp [hc, or_iff_left_of_imp (this _)]

end NormedSpaceOverCompleteField

section NormedRing

variable {𝕜 : Type*} [NormedRing 𝕜] {f : α -> 𝕜}

@[fun_prop]
/--
theorem `Integrable.const_mul` / 定理 `Integrable.const_mul`

English:
theorem Integrable.const_mul
  given: {f : α -> 𝕜} (h : Integrable f μ) (c : 𝕜)
  proof: h.smul c

@[fun_prop]

中文:
定理 可积.const_mul
  条件: {f : α -> 𝕜} (h : 可积 f μ) (c : 𝕜)
  证明: h.smul c

@[fun_prop]

Depends on / 依赖: h.smul
-/
theorem Integrable.const_mul {f : α -> 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (fun x => c * f x) μ :=
  h.smul c

@[fun_prop]
/--
theorem `Integrable.const_mul'` / 定理 `Integrable.const_mul'`

English:
theorem Integrable.const_mul'
  given: {f : α -> 𝕜} (h : Integrable f μ) (c : 𝕜)
  proof: Integrable.const_mul h c

@[fun_prop]

中文:
定理 可积.const_mul'
  条件: {f : α -> 𝕜} (h : 可积 f μ) (c : 𝕜)
  证明: Integrable.const_mul h c

@[fun_prop]

Depends on / 依赖: Integrable, Integrable.const_mul, const_mul
-/
theorem Integrable.const_mul' {f : α -> 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable ((fun _ : α => c) * f) μ :=
  Integrable.const_mul h c

@[fun_prop]
/--
theorem `Integrable.mul_const` / 定理 `Integrable.mul_const`

English:
theorem Integrable.mul_const
  given: {f : α -> 𝕜} (h : Integrable f μ) (c : 𝕜)
  proof: h.smul (MulOpposite.op c)

@[fun_prop]

中文:
定理 可积.mul_const
  条件: {f : α -> 𝕜} (h : 可积 f μ) (c : 𝕜)
  证明: h.smul (MulOpposite.op c)

@[fun_prop]

Depends on / 依赖: MulOpposite, MulOpposite.op, h.smul
-/
theorem Integrable.mul_const {f : α -> 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (fun x => f x * c) μ :=
  h.smul (MulOpposite.op c)

@[fun_prop]
/--
theorem `Integrable.mul_const'` / 定理 `Integrable.mul_const'`

English:
theorem Integrable.mul_const'
  given: {f : α -> 𝕜} (h : Integrable f μ) (c : 𝕜)
  proof: Integrable.mul_const h c

中文:
定理 可积.mul_const'
  条件: {f : α -> 𝕜} (h : 可积 f μ) (c : 𝕜)
  证明: Integrable.mul_const h c

Depends on / 依赖: Integrable, Integrable.mul_const, mul_const
-/
theorem Integrable.mul_const' {f : α -> 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (f * fun _ : α => c) μ :=
  Integrable.mul_const h c

/--
theorem `integrable_const_mul_iff` / 定理 `integrable_const_mul_iff`

English:
theorem integrable_const_mul_iff
  given: {c : 𝕜} (hc : IsUnit c) (f : α -> 𝕜)
  proof: hc.integrable_smul_iff f

中文:
定理 integrable_const_mul_iff
  条件: {c : 𝕜} (hc : 是单位 c) (f : α -> 𝕜)
  证明: hc.integrable_smul_iff f

Depends on / 依赖: hc.integrable_smul_iff, integrable_smul_iff
-/
theorem integrable_const_mul_iff {c : 𝕜} (hc : IsUnit c) (f : α -> 𝕜) :
    Integrable (fun x => c * f x) μ ↔ Integrable f μ :=
  hc.integrable_smul_iff f

/--
theorem `integrable_mul_const_iff` / 定理 `integrable_mul_const_iff`

English:
theorem integrable_mul_const_iff
  given: {c : 𝕜} (hc : IsUnit c) (f : α -> 𝕜)
  proof: hc.op.integrable_smul_iff f

中文:
定理 integrable_mul_const_iff
  条件: {c : 𝕜} (hc : 是单位 c) (f : α -> 𝕜)
  证明: hc.op.integrable_smul_iff f

Depends on / 依赖: hc.op.integrable_smul_iff, integrable_smul_iff
-/
theorem integrable_mul_const_iff {c : 𝕜} (hc : IsUnit c) (f : α -> 𝕜) :
    Integrable (fun x => f x * c) μ ↔ Integrable f μ :=
  hc.op.integrable_smul_iff f

-- TODO: generalise this to enorms, once there is an `ENormedDivisionRing` class
/--
theorem `Integrable.bdd_mul` / 定理 `Integrable.bdd_mul`

English:
theorem Integrable.bdd_mul
  statement: {f g : α -> 𝕜} {c : Real} (hg : Integrable g μ)
  proof: hg.bdd_smul c hf hf_bound

中文:
定理 可积.bdd_mul
  结论: {f g : α -> 𝕜} {c : 实数} (hg : 可积 g μ)
  证明: hg.bdd_smul c hf hf_bound

Depends on / 依赖: bdd_smul, hf_bound, hg.bdd_smul
-/
theorem Integrable.bdd_mul {f g : α -> 𝕜} {c : Real} (hg : Integrable g μ)
    (hf : AEStronglyMeasurable f μ) (hf_bound : forallᵐ x ∂μ, ‖f x‖ <= c) :
    Integrable (fun x => f x * g x) μ :=
  hg.bdd_smul c hf hf_bound

/--
theorem `Integrable.mul_bdd` / 定理 `Integrable.mul_bdd`

English:
theorem Integrable.mul_bdd
  statement: {f g : α -> 𝕜} {c : Real} (hf : Integrable f μ)
  proof: hf.smul_bdd c hg hg_bound

中文:
定理 可积.mul_bdd
  结论: {f g : α -> 𝕜} {c : 实数} (hf : 可积 f μ)
  证明: hf.smul_bdd c hg hg_bound

Depends on / 依赖: hf.smul_bdd, hg_bound, smul_bdd
-/
theorem Integrable.mul_bdd {f g : α -> 𝕜} {c : Real} (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (hg_bound : forallᵐ x ∂μ, ‖g x‖ <= c) :
    Integrable (fun x => f x * g x) μ :=
  hf.smul_bdd c hg hg_bound

/--
theorem `Integrable.mul_of_top_right` / 定理 `Integrable.mul_of_top_right`

English:
theorem Integrable.mul_of_top_right
  statement: {f : α -> 𝕜} {φ : α -> 𝕜} (hf : Integrable f μ)
  proof: hf.smul_of_top_right hφ

中文:
定理 可积.mul_of_top_right
  结论: {f : α -> 𝕜} {φ : α -> 𝕜} (hf : 可积 f μ)
  证明: hf.smul_of_top_right hφ

Depends on / 依赖: hf.smul_of_top_right, smul_of_top_right
-/
theorem Integrable.mul_of_top_right {f : α -> 𝕜} {φ : α -> 𝕜} (hf : Integrable f μ)
    (hφ : MemLp φ ∞ μ) : Integrable (φ * f) μ :=
  hf.smul_of_top_right hφ

/--
theorem `Integrable.mul_of_top_left` / 定理 `Integrable.mul_of_top_left`

English:
theorem Integrable.mul_of_top_left
  statement: {f : α -> 𝕜} {φ : α -> 𝕜} (hφ : Integrable φ μ)
  proof: hφ.smul_of_top_left hf

中文:
定理 可积.mul_of_top_left
  结论: {f : α -> 𝕜} {φ : α -> 𝕜} (hφ : 可积 φ μ)
  证明: hφ.smul_of_top_left hf

Depends on / 依赖: smul_of_top_left
-/
theorem Integrable.mul_of_top_left {f : α -> 𝕜} {φ : α -> 𝕜} (hφ : Integrable φ μ)
    (hf : MemLp f ∞ μ) : Integrable (φ * f) μ :=
  hφ.smul_of_top_left hf

/--
lemma `MemLp.integrable_mul` / 引理 `MemLp.integrable_mul`

English:
lemma MemLp.integrable_mul
  statement: {p q : Real>=0∞} {f g : α -> 𝕜} (hf : MemLp f p μ) (hg : MemLp g q μ)
  proof: memLp_one_iff_integrable.1 hg.mul hf

中文:
引理 MemLp.integrable_mul
  结论: {p q : 实数>=0∞} {f g : α -> 𝕜} (hf : MemLp f p μ) (hg : MemLp g q μ)
  证明: memLp_one_iff_integrable.1 hg.mul hf

Depends on / 依赖: hg.mul, memLp_one_iff_integrable
-/
lemma MemLp.integrable_mul {p q : Real>=0∞} {f g : α -> 𝕜} (hf : MemLp f p μ) (hg : MemLp g q μ)
    [HolderTriple p q 1] :
    Integrable (f * g) μ :=
memLp_one_iff_integrable.1 hg.mul hf

end NormedRing

section NormedDivisionRing

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] {f : α -> 𝕜}

@[fun_prop]
/--
theorem `Integrable.div_const` / 定理 `Integrable.div_const`

English:
theorem Integrable.div_const
  given: {f : α -> 𝕜} (h : Integrable f μ) (c : 𝕜)
  proof: by simp_rw [div_eq_mul_inv, h.mul_const]

中文:
定理 可积.div_const
  条件: {f : α -> 𝕜} (h : 可积 f μ) (c : 𝕜)
  证明: by simp_rw [div_eq_mul_inv, h.mul_const]

Depends on / 依赖: div_eq_mul_inv, h.mul_const, mul_const, simp_rw
-/
theorem Integrable.div_const {f : α -> 𝕜} (h : Integrable f μ) (c : 𝕜) :
    Integrable (fun x => f x / c) μ := by simp_rw [div_eq_mul_inv, h.mul_const]

end NormedDivisionRing

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {f : α -> 𝕜}

@[fun_prop]
/--
theorem `Integrable.ofReal` / 定理 `Integrable.ofReal`

English:
theorem Integrable.ofReal
  given: {f : α -> Real} (hf : Integrable f μ)
  proof: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.ofReal

中文:
定理 可积.of实数
  条件: {f : α -> 实数} (hf : 可积 f μ)
  证明: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.ofReal

Depends on / 依赖: hf.ofReal, memLp_one_iff_integrable, ofReal
-/
theorem Integrable.ofReal {f : α -> Real} (hf : Integrable f μ) :
    Integrable (fun x => (f x : 𝕜)) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.ofReal

/--
theorem `Integrable.re_im_iff` / 定理 `Integrable.re_im_iff`

English:
theorem Integrable.re_im_iff
  proof: by
  simp_rw [← memLp_one_iff_integrable]
  exact memLp_re_im_iff

@[fun_prop]

中文:
定理 可积.re_im_iff
  证明: by
  simp_rw [← memLp_one_iff_integrable]
  exact memLp_re_im_iff

@[fun_prop]

Depends on / 依赖: memLp_one_iff_integrable, memLp_re_im_iff, simp_rw
-/
theorem Integrable.re_im_iff :
    Integrable (fun x => RCLike.re (f x)) μ ∧ Integrable (fun x => RCLike.im (f x)) μ ↔
      Integrable f μ := by
  simp_rw [← memLp_one_iff_integrable]
  exact memLp_re_im_iff

@[fun_prop]
/--
theorem `Integrable.re` / 定理 `Integrable.re`

English:
theorem Integrable.re
  given: (hf : Integrable f μ)
  statement: Integrable (fun x => RCLike.re (f x)) μ
  proof: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.re

@[fun_prop]

中文:
定理 可积.re
  条件: (hf : 可积 f μ)
  结论: 可积 (fun x => RCLike.re (f x)) μ
  证明: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.re

@[fun_prop]

Depends on / 依赖: hf.re, memLp_one_iff_integrable
-/
theorem Integrable.re (hf : Integrable f μ) : Integrable (fun x => RCLike.re (f x)) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.re

@[fun_prop]
/--
theorem `Integrable.im` / 定理 `Integrable.im`

English:
theorem Integrable.im
  given: (hf : Integrable f μ)
  statement: Integrable (fun x => RCLike.im (f x)) μ
  proof: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.im

中文:
定理 可积.im
  条件: (hf : 可积 f μ)
  结论: 可积 (fun x => RCLike.im (f x)) μ
  证明: by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.im

Depends on / 依赖: hf.im, memLp_one_iff_integrable
-/
theorem Integrable.im (hf : Integrable f μ) : Integrable (fun x => RCLike.im (f x)) μ := by
  rw [← memLp_one_iff_integrable] at hf ⊢
  exact hf.im

end RCLike

section Trim

variable {H : Type*} [NormedAddCommGroup H] {m0 : MeasurableSpace α} {μ' : Measure α} {f : α -> H}

/--
theorem `Integrable.trim` / 定理 `Integrable.trim`

English:
theorem Integrable.trim
  given: (hm : m <= m0) (hf_int : Integrable f μ') (hf : StronglyMeasurable[m] f)
  proof: by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]; rw [lintegral_trim hm _]
  · exact hf_int.2
  · fun_prop

中文:
定理 可积.trim
  条件: (hm : m <= m0) (hf_int : 可积 f μ') (hf : StronglyMeasurable[m] f)
  证明: by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]; rw [lintegral_trim hm _]
  · exact hf_int.2
  · fun_prop

Depends on / 依赖: HasFiniteIntegral, aestronglyMeasurable, fun_prop, hf.aestronglyMeasurable, hf_int, lintegral_trim
-/
theorem Integrable.trim (hm : m <= m0) (hf_int : Integrable f μ') (hf : StronglyMeasurable[m] f) :
    Integrable f (μ'.trim hm) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]; rw [lintegral_trim hm _]
  · exact hf_int.2
  · fun_prop

/--
theorem `integrable_of_integrable_trim` / 定理 `integrable_of_integrable_trim`

English:
theorem integrable_of_integrable_trim
  given: (hm : m <= m0) (hf_int : Integrable f (μ'.trim hm))
  proof: by
  obtain ⟨hf_meas_ae, hf⟩ := hf_int
  refine ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim hm hf_meas_ae, ?_⟩
  simpa [HasFiniteIntegral, lintegral_trim_ae hm hf_meas_ae.enorm] using hf

中文:
定理 integrable_of_integrable_trim
  条件: (hm : m <= m0) (hf_int : 可积 f (μ'.trim hm))
  证明: by
  obtain ⟨hf_meas_ae, hf⟩ := hf_int
  refine ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim hm hf_meas_ae, ?_⟩
  simpa [HasFiniteIntegral, lintegral_trim_ae hm hf_meas_ae.enorm] using hf

Depends on / 依赖: HasFiniteIntegral, aestronglyMeasurable_of_aestronglyMeasurable_trim, hf_int, hf_meas_ae, hf_meas_ae.enorm, lintegral_trim_ae
-/
theorem integrable_of_integrable_trim (hm : m <= m0) (hf_int : Integrable f (μ'.trim hm)) :
    Integrable f μ' := by
  obtain ⟨hf_meas_ae, hf⟩ := hf_int
  refine ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim hm hf_meas_ae, ?_⟩
  simpa [HasFiniteIntegral, lintegral_trim_ae hm hf_meas_ae.enorm] using hf

end Trim

section SigmaFinite

variable {E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E]
  {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]

/--
theorem `integrable_of_forall_fin_meas_le'` / 定理 `integrable_of_forall_fin_meas_le'`

English:
theorem integrable_of_forall_fin_meas_le'
  statement: {μ : Measure α} (hm : m <= m0) [SigmaFinite (μ.trim hm)]
  proof: ⟨hf_meas, (lintegral_le_of_forall_fin_meas_trim_le hm C hf).trans_lt hC⟩

中文:
定理 integrable_of_对任意_fin_meas_le'
  结论: {μ : 测度 α} (hm : m <= m0) [σ有限 (μ.trim hm)]
  证明: ⟨hf_meas, (lintegral_le_of_forall_fin_meas_trim_le hm C hf).trans_lt hC⟩

Depends on / 依赖: hf_meas, lintegral_le_of_forall_fin_meas_trim_le, trans_lt
-/
theorem integrable_of_forall_fin_meas_le' {μ : Measure α} (hm : m <= m0) [SigmaFinite (μ.trim hm)]
    (C : Real>=0∞) (hC : C < ∞) {f : α -> ε} (hf_meas : AEStronglyMeasurable f μ)
    (hf : forall s, MeasurableSet[m] s -> μ s != ∞ -> ∫⁻ x in s, ‖f x‖ₑ ∂μ <= C) : Integrable f μ :=
  ⟨hf_meas, (lintegral_le_of_forall_fin_meas_trim_le hm C hf).trans_lt hC⟩

/--
theorem `integrable_of_forall_fin_meas_le` / 定理 `integrable_of_forall_fin_meas_le`

English:
theorem integrable_of_forall_fin_meas_le
  statement: [SigmaFinite μ] (C : Real>=0∞) (hC : C < ∞) {f : α -> ε}
  proof: have : SigmaFinite (μ.trim le_rfl) := by rwa [@trim_eq_self _ m]
  integrable_of_forall_fin_meas_le' le_rfl C hC hf_meas hf

中文:
定理 integrable_of_对任意_fin_meas_le
  结论: [σ有限 μ] (C : 实数>=0∞) (hC : C < ∞) {f : α -> ε}
  证明: have : SigmaFinite (μ.trim le_rfl) := by rwa [@trim_eq_self _ m]
  integrable_of_forall_fin_meas_le' le_rfl C hC hf_meas hf

Depends on / 依赖: SigmaFinite, hf_meas, integrable_of_forall_fin_meas_le, le_rfl, trim_eq_self
-/
theorem integrable_of_forall_fin_meas_le [SigmaFinite μ] (C : Real>=0∞) (hC : C < ∞) {f : α -> ε}
    (hf_meas : AEStronglyMeasurable[m] f μ)
    (hf : forall s : Set α, MeasurableSet[m] s -> μ s != ∞ -> ∫⁻ x in s, ‖f x‖ₑ ∂μ <= C) :
    Integrable f μ :=
  have : SigmaFinite (μ.trim le_rfl) := by rwa [@trim_eq_self _ m]
  integrable_of_forall_fin_meas_le' le_rfl C hC hf_meas hf

end SigmaFinite

section restrict

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε] {f : α -> ε}

/--
lemma `Integrable.restrict` / 引理 `Integrable.restrict`

English:
lemma Integrable.restrict
  given: (hf : Integrable f μ) {s : Set α}
  statement: Integrable f (μ.restrict s)
  proof: hf.mono_measure Measure.restrict_le_self

中文:
引理 可积.restrict
  条件: (hf : 可积 f μ) {s : 集合 α}
  结论: 可积 f (μ.restrict s)
  证明: hf.mono_measure Measure.restrict_le_self

Depends on / 依赖: Measure, Measure.restrict_le_self, hf.mono_measure, mono_measure, restrict_le_self
-/
lemma Integrable.restrict (hf : Integrable f μ) {s : Set α} : Integrable f (μ.restrict s) :=
  hf.mono_measure Measure.restrict_le_self

end restrict

end MeasureTheory

section ContinuousLinearMap

open MeasureTheory

variable {E H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup H]
  {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedSpace 𝕜' E] [NormedSpace 𝕜 H]

variable {σ : 𝕜 ->+* 𝕜'} {σ' : 𝕜' ->+* 𝕜} [RingHomIsometric σ] [RingHomIsometric σ']
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

@[fun_prop]
/--
theorem `ContinuousLinearMap.integrable_comp` / 定理 `ContinuousLinearMap.integrable_comp`

English:
theorem ContinuousLinearMap.integrable_comp
  given: {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ)
  proof: ((Integrable.norm φ_int).const_mul ‖L‖).mono'
    (by fun_prop)
    (Eventually.of_forall fun a => L.le_opNorm (φ a))

@[simp]

中文:
定理 连续线性映射.integrable_comp
  条件: {φ : α -> H} (L : H ->SL[σ] E) (φ_int : 可积 φ μ)
  证明: ((Integrable.norm φ_int).const_mul ‖L‖).mono'
    (by fun_prop)
    (Eventually.of_forall fun a => L.le_opNorm (φ a))

@[simp]

Depends on / 依赖: Eventually, Eventually.of_forall, Integrable, Integrable.norm, L.le_opNorm, const_mul, fun_prop, le_opNorm, of_forall
-/
theorem ContinuousLinearMap.integrable_comp {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) :
    Integrable (fun a : α => L (φ a)) μ :=
  ((Integrable.norm φ_int).const_mul ‖L‖).mono'
    (by fun_prop)
    (Eventually.of_forall fun a => L.le_opNorm (φ a))

@[simp]
/--
theorem `ContinuousLinearEquiv.integrable_comp_iff` / 定理 `ContinuousLinearEquiv.integrable_comp_iff`

English:
theorem ContinuousLinearEquiv.integrable_comp_iff
  given: {φ : α -> H} (L : H ≃SL[σ] E)
  proof: ⟨fun h => by simpa using ContinuousLinearMap.integrable_comp (L.symm : E ->SL[σ'] H) h,
  fun h => ContinuousLinearMap.integrable_comp (L : H ->SL[σ] E) h⟩

@[simp]

中文:
定理 连续线性等价.integrable_comp_iff
  条件: {φ : α -> H} (L : H ≃SL[σ] E)
  证明: ⟨fun h => by simpa using ContinuousLinearMap.integrable_comp (L.symm : E ->SL[σ'] H) h,
  fun h => ContinuousLinearMap.integrable_comp (L : H ->SL[σ] E) h⟩

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.integrable_comp, L.symm, integrable_comp
-/
theorem ContinuousLinearEquiv.integrable_comp_iff {φ : α -> H} (L : H ≃SL[σ] E) :
    Integrable (fun a : α => L (φ a)) μ ↔ Integrable φ μ :=
  ⟨fun h => by simpa using ContinuousLinearMap.integrable_comp (L.symm : E ->SL[σ'] H) h,
  fun h => ContinuousLinearMap.integrable_comp (L : H ->SL[σ] E) h⟩

@[simp]
/--
theorem `LinearIsometryEquiv.integrable_comp_iff` / 定理 `LinearIsometryEquiv.integrable_comp_iff`

English:
theorem LinearIsometryEquiv.integrable_comp_iff
  given: {φ : α -> H} (L : H ≃ₛₗᵢ[σ] E)
  proof: ContinuousLinearEquiv.integrable_comp_iff (L : H ≃SL[σ] E)

中文:
定理 线性等距等价.integrable_comp_iff
  条件: {φ : α -> H} (L : H ≃ₛₗᵢ[σ] E)
  证明: ContinuousLinearEquiv.integrable_comp_iff (L : H ≃SL[σ] E)

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.integrable_comp_iff, integrable_comp_iff
-/
theorem LinearIsometryEquiv.integrable_comp_iff {φ : α -> H} (L : H ≃ₛₗᵢ[σ] E) :
    Integrable (fun a : α => L (φ a)) μ ↔ Integrable φ μ :=
  ContinuousLinearEquiv.integrable_comp_iff (L : H ≃SL[σ] E)

/--
theorem `MeasureTheory.Integrable.apply_continuousLinearMap` / 定理 `MeasureTheory.Integrable.apply_continuousLinearMap`

English:
theorem MeasureTheory.Integrable.apply_continuousLinearMap
  statement: {φ : α -> H ->SL[σ] E}
  proof: (ContinuousLinearMap.apply' E σ v).integrable_comp φ_int

中文:
定理 测度论.可积.apply_continuousLinearMap
  结论: {φ : α -> H ->SL[σ] E}
  证明: (ContinuousLinearMap.apply' E σ v).integrable_comp φ_int

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.apply, integrable_comp
-/
theorem MeasureTheory.Integrable.apply_continuousLinearMap {φ : α -> H ->SL[σ] E}
    (φ_int : Integrable φ μ) (v : H) : Integrable (fun a => φ a v) μ :=
  (ContinuousLinearMap.apply' E σ v).integrable_comp φ_int

end ContinuousLinearMap

namespace MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

@[fun_prop]
/--
lemma `Integrable.fst` / 引理 `Integrable.fst`

English:
lemma Integrable.fst
  given: {f : α -> E × F} (hf : Integrable f μ)
  statement: Integrable (fun x => (f x).1) μ
  proof: (ContinuousLinearMap.fst Real E F).integrable_comp hf

@[fun_prop]

中文:
引理 可积.fst
  条件: {f : α -> E × F} (hf : 可积 f μ)
  结论: 可积 (fun x => (f x).1) μ
  证明: (ContinuousLinearMap.fst Real E F).integrable_comp hf

@[fun_prop]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.fst, integrable_comp
-/
lemma Integrable.fst {f : α -> E × F} (hf : Integrable f μ) : Integrable (fun x => (f x).1) μ :=
  (ContinuousLinearMap.fst Real E F).integrable_comp hf

@[fun_prop]
/--
lemma `Integrable.snd` / 引理 `Integrable.snd`

English:
lemma Integrable.snd
  given: {f : α -> E × F} (hf : Integrable f μ)
  statement: Integrable (fun x => (f x).2) μ
  proof: (ContinuousLinearMap.snd Real E F).integrable_comp hf

中文:
引理 可积.snd
  条件: {f : α -> E × F} (hf : 可积 f μ)
  结论: 可积 (fun x => (f x).2) μ
  证明: (ContinuousLinearMap.snd Real E F).integrable_comp hf

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.snd, integrable_comp
-/
lemma Integrable.snd {f : α -> E × F} (hf : Integrable f μ) : Integrable (fun x => (f x).2) μ :=
  (ContinuousLinearMap.snd Real E F).integrable_comp hf

/--
lemma `integrable_prod` / 引理 `integrable_prod`

English:
lemma integrable_prod
  given: {f : α -> E × F}
  proof: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

中文:
引理 integrable_prod
  条件: {f : α -> E × F}
  证明: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

Depends on / 依赖: h.fst, h.snd, prodMk
-/
lemma integrable_prod {f : α -> E × F} :
    Integrable f μ ↔ Integrable (fun x => (f x).1) μ ∧ Integrable (fun x => (f x).2) μ :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

section Limit

/--
theorem `lintegral_enorm_le_liminf_of_tendsto` / 定理 `lintegral_enorm_le_liminf_of_tendsto`

English:
theorem lintegral_enorm_le_liminf_of_tendsto
  proof: lintegral_congr_ae (by filter_upwards [hGf] with x hx using hx.enorm.liminf_eq) ▸
    (MeasureTheory.lintegral_liminf_le' hG)

中文:
定理 lintegral_enorm_le_liminf_of_tendsto
  证明: lintegral_congr_ae (by filter_upwards [hGf] with x hx using hx.enorm.liminf_eq) ▸
    (MeasureTheory.lintegral_liminf_le' hG)

Depends on / 依赖: MeasureTheory, MeasureTheory.lintegral_liminf_le, filter_upwards, hx.enorm.liminf_eq, liminf_eq, lintegral_congr_ae, lintegral_liminf_le
-/
theorem lintegral_enorm_le_liminf_of_tendsto
    {G : Nat -> Real -> Real} {f : Real -> Real} {μ : Measure Real}
    (hGf : forallᵐ x ∂μ, Tendsto (fun (n : Nat) => G n x) atTop (𝓝 (f x)))
    (hG : forall (n : Nat), AEMeasurable (fun x => ‖G n x‖ₑ) μ) :
    ∫⁻ x, ‖f x‖ₑ ∂μ <= liminf (fun n => ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop :=
  lintegral_congr_ae (by filter_upwards [hGf] with x hx using hx.enorm.liminf_eq) ▸
    (MeasureTheory.lintegral_liminf_le' hG)

/--
theorem `integrable_of_tendsto` / 定理 `integrable_of_tendsto`

English:
theorem integrable_of_tendsto
  proof: ⟨aestronglyMeasurable_of_tendsto_ae _ hG hGf,
   lt_of_le_of_lt (lintegral_enorm_le_liminf_of_tendsto hGf
    (fun n => (hG n).aemeasurable.enorm)) hG'.lt_top⟩

中文:
定理 integrable_of_tendsto
  证明: ⟨aestronglyMeasurable_of_tendsto_ae _ hG hGf,
   lt_of_le_of_lt (lintegral_enorm_le_liminf_of_tendsto hGf
    (fun n => (hG n).aemeasurable.enorm)) hG'.lt_top⟩

Depends on / 依赖: aemeasurable, aemeasurable.enorm, aestronglyMeasurable_of_tendsto_ae, lintegral_enorm_le_liminf_of_tendsto, lt_of_le_of_lt, lt_top
-/
theorem integrable_of_tendsto
    {G : Nat -> Real -> Real} {f : Real -> Real} {μ : Measure Real}
    (hGf : forallᵐ x ∂μ, Tendsto (fun (n : Nat) => G n x) atTop (𝓝 (f x)))
    (hG : forall (n : Nat), AEStronglyMeasurable (G n) μ)
    (hG' : liminf (fun n => ∫⁻ x, ‖G n x‖ₑ ∂μ) atTop != ⊤) :
    Integrable f μ :=
  ⟨aestronglyMeasurable_of_tendsto_ae _ hG hGf,
   lt_of_le_of_lt (lintegral_enorm_le_liminf_of_tendsto hGf
    (fun n => (hG n).aemeasurable.enorm)) hG'.lt_top⟩

end Limit

end MeasureTheory
