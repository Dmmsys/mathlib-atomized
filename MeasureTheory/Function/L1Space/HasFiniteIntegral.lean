/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Function with finite integral

In this file we define the predicate `HasFiniteIntegral`, which is then used to define the
predicate `Integrable` in the corresponding file.

## Main definition

* Let `f : α → β` be a function, where `α` is a `MeasureSpace` and `β` a `NormedAddCommGroup`.
  Then `HasFiniteIntegral f` means `∫⁻ a, ‖f a‖ₑ < ∞`.

## Tags

finite integral

-/

@[expose] public section

noncomputable section

open Topology ENNReal MeasureTheory NNReal

open Set Filter TopologicalSpace ENNReal EMetric MeasureTheory

variable {α β γ ε ε' ε'' : Type*} {m : MeasurableSpace α} {μ ν : Measure α}
variable [NormedAddCommGroup β] [NormedAddCommGroup γ] [ENorm ε] [ENorm ε']
  [TopologicalSpace ε''] [ESeminormedAddMonoid ε'']

namespace MeasureTheory


/--
lemma `lintegral_enorm_eq_lintegral_edist` / 引理 `lintegral_enorm_eq_lintegral_edist`

English:
lemma lintegral_enorm_eq_lintegral_edist
  given: (f : α -> β)
  proof: by simp only [edist_zero_right]

中文:
引理 lintegral_enorm_eq_lintegral_edist
  条件: (f : α -> β)
  证明: by simp only [edist_zero_right]

Depends on / 依赖: edist_zero_right
-/
lemma lintegral_enorm_eq_lintegral_edist (f : α -> β) :
    ∫⁻ a, ‖f a‖ₑ ∂μ = ∫⁻ a, edist (f a) 0 ∂μ := by simp only [edist_zero_right]

/--
theorem `lintegral_norm_eq_lintegral_edist` / 定理 `lintegral_norm_eq_lintegral_edist`

English:
theorem lintegral_norm_eq_lintegral_edist
  given: (f : α -> β)
  proof: by
  simp only [ofReal_norm, edist_zero_right]

中文:
定理 lintegral_norm_eq_lintegral_edist
  条件: (f : α -> β)
  证明: by
  simp only [ofReal_norm, edist_zero_right]

Depends on / 依赖: edist_zero_right, ofReal_norm
-/
theorem lintegral_norm_eq_lintegral_edist (f : α -> β) :
    ∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ = ∫⁻ a, edist (f a) 0 ∂μ := by
  simp only [ofReal_norm, edist_zero_right]

/--
theorem `lintegral_edist_triangle` / 定理 `lintegral_edist_triangle`

English:
theorem lintegral_edist_triangle
  statement: {f g h : α -> β} (hf : AEStronglyMeasurable f μ)
  proof: by
  rw [← lintegral_add_left' (hf.edist hh)]
  refine lintegral_mono fun a => ?_
  apply edist_triangle_right

中文:
定理 lintegral_edist_triangle
  结论: {f g h : α -> β} (hf : AEStronglyMeasurable f μ)
  证明: by
  rw [← lintegral_add_left' (hf.edist hh)]
  refine lintegral_mono fun a => ?_
  apply edist_triangle_right

Depends on / 依赖: edist_triangle_right, hf.edist, lintegral_add_left, lintegral_mono
-/
theorem lintegral_edist_triangle {f g h : α -> β} (hf : AEStronglyMeasurable f μ)
    (hh : AEStronglyMeasurable h μ) :
    (∫⁻ a, edist (f a) (g a) ∂μ) <= (∫⁻ a, edist (f a) (h a) ∂μ) + ∫⁻ a, edist (g a) (h a) ∂μ := by
  rw [← lintegral_add_left' (hf.edist hh)]
  refine lintegral_mono fun a => ?_
  apply edist_triangle_right

-- Yaël: Why do the following four lemmas even exist?
/--
theorem `lintegral_enorm_zero` / 定理 `lintegral_enorm_zero`

English:
theorem lintegral_enorm_zero
  statement: ∫⁻ _ : α, ‖(0 : ε'')‖ₑ ∂μ = 0
  proof: by simp

中文:
定理 lintegral_enorm_zero
  结论: ∫⁻ _ : α, ‖(0 : ε'')‖ₑ ∂μ = 0
  证明: by simp
-/
theorem lintegral_enorm_zero : ∫⁻ _ : α, ‖(0 : ε'')‖ₑ ∂μ = 0 := by simp

/--
theorem `lintegral_enorm_add_left` / 定理 `lintegral_enorm_add_left`

English:
theorem lintegral_enorm_add_left
  given: {f : α -> ε''} (hf : AEStronglyMeasurable f μ) (g : α -> ε')
  proof: lintegral_add_left' hf.enorm _

中文:
定理 lintegral_enorm_add_left
  条件: {f : α -> ε''} (hf : AEStronglyMeasurable f μ) (g : α -> ε')
  证明: lintegral_add_left' hf.enorm _

Depends on / 依赖: hf.enorm, lintegral_add_left
-/
theorem lintegral_enorm_add_left {f : α -> ε''} (hf : AEStronglyMeasurable f μ) (g : α -> ε') :
    ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ + ∫⁻ a, ‖g a‖ₑ ∂μ :=
  lintegral_add_left' hf.enorm _

/--
theorem `lintegral_enorm_add_right` / 定理 `lintegral_enorm_add_right`

English:
theorem lintegral_enorm_add_right
  given: (f : α -> ε') {g : α -> ε''} (hg : AEStronglyMeasurable g μ)
  proof: lintegral_add_right' _ hg.enorm

中文:
定理 lintegral_enorm_add_right
  条件: (f : α -> ε') {g : α -> ε''} (hg : AEStronglyMeasurable g μ)
  证明: lintegral_add_right' _ hg.enorm

Depends on / 依赖: hg.enorm, lintegral_add_right
-/
theorem lintegral_enorm_add_right (f : α -> ε') {g : α -> ε''} (hg : AEStronglyMeasurable g μ) :
    ∫⁻ a, ‖f a‖ₑ + ‖g a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ + ∫⁻ a, ‖g a‖ₑ ∂μ :=
  lintegral_add_right' _ hg.enorm

/--
theorem `lintegral_enorm_neg` / 定理 `lintegral_enorm_neg`

English:
theorem lintegral_enorm_neg
  given: {f : α -> β}
  statement: ∫⁻ a, ‖(-f) a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ
  proof: by simp

中文:
定理 lintegral_enorm_neg
  条件: {f : α -> β}
  结论: ∫⁻ a, ‖(-f) a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ
  证明: by simp
-/
theorem lintegral_enorm_neg {f : α -> β} : ∫⁻ a, ‖(-f) a‖ₑ ∂μ = ∫⁻ a, ‖f a‖ₑ ∂μ := by simp

/-! ### The predicate `HasFiniteIntegral` -/


/-- `HasFiniteIntegral f μ` means that the integral `∫⁻ a, ‖f a‖ ∂μ` is finite.
  `HasFiniteIntegral f` means `HasFiniteIntegral f volume`. -/
@[fun_prop]
/--
Definition of `HasFiniteIntegral` / `HasFiniteIntegral` 的定义

English:
definition HasFiniteIntegral
  signature: {_ : MeasurableSpace α} (f : α -> ε)
  body: ∫⁻ a, ‖f a‖ₑ ∂μ < ∞

中文:
定义 HasFinite整数egral
  签名: {_ : 可测空间 α} (f : α -> ε)
  定义体: ∫⁻ a, ‖f a‖ₑ ∂μ < ∞

Depends on / 依赖: volume_tac
-/
def HasFiniteIntegral {_ : MeasurableSpace α} (f : α -> ε)
    (μ : Measure α := by volume_tac) : Prop :=
  ∫⁻ a, ‖f a‖ₑ ∂μ < ∞

/--
theorem `hasFiniteIntegral_def` / 定理 `hasFiniteIntegral_def`

English:
theorem hasFiniteIntegral_def
  given: {_ : MeasurableSpace α} (f : α -> ε) (μ : Measure α)
  proof: Iff.rfl

中文:
定理 hasFinite整数egral_def
  条件: {_ : 可测空间 α} (f : α -> ε) (μ : 测度 α)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem hasFiniteIntegral_def {_ : MeasurableSpace α} (f : α -> ε) (μ : Measure α) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, ‖f a‖ₑ ∂μ < ∞) :=
  Iff.rfl

/--
theorem `hasFiniteIntegral_iff_enorm` / 定理 `hasFiniteIntegral_iff_enorm`

English:
theorem hasFiniteIntegral_iff_enorm
  given: {f : α -> ε}
  statement: HasFiniteIntegral f μ ↔ ∫⁻ a, ‖f a‖ₑ ∂μ < ∞
  proof: by
  simp only [HasFiniteIntegral]

中文:
定理 hasFinite整数egral_iff_enorm
  条件: {f : α -> ε}
  结论: HasFinite整数egral f μ ↔ ∫⁻ a, ‖f a‖ₑ ∂μ < ∞
  证明: by
  simp only [HasFiniteIntegral]

Depends on / 依赖: HasFiniteIntegral
-/
theorem hasFiniteIntegral_iff_enorm {f : α -> ε} : HasFiniteIntegral f μ ↔ ∫⁻ a, ‖f a‖ₑ ∂μ < ∞ := by
  simp only [HasFiniteIntegral]

/--
theorem `hasFiniteIntegral_iff_norm` / 定理 `hasFiniteIntegral_iff_norm`

English:
theorem hasFiniteIntegral_iff_norm
  given: (f : α -> β)
  proof: by
  simp only [hasFiniteIntegral_iff_enorm, ofReal_norm]

中文:
定理 hasFinite整数egral_iff_norm
  条件: (f : α -> β)
  证明: by
  simp only [hasFiniteIntegral_iff_enorm, ofReal_norm]

Depends on / 依赖: hasFiniteIntegral_iff_enorm, ofReal_norm
-/
theorem hasFiniteIntegral_iff_norm (f : α -> β) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) < ∞ := by
  simp only [hasFiniteIntegral_iff_enorm, ofReal_norm]

/--
theorem `hasFiniteIntegral_iff_edist` / 定理 `hasFiniteIntegral_iff_edist`

English:
theorem hasFiniteIntegral_iff_edist
  given: (f : α -> β)
  proof: by
  simp only [hasFiniteIntegral_iff_norm, edist_dist, dist_zero_right]

中文:
定理 hasFinite整数egral_iff_edist
  条件: (f : α -> β)
  证明: by
  simp only [hasFiniteIntegral_iff_norm, edist_dist, dist_zero_right]

Depends on / 依赖: dist_zero_right, edist_dist, hasFiniteIntegral_iff_norm
-/
theorem hasFiniteIntegral_iff_edist (f : α -> β) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, edist (f a) 0 ∂μ) < ∞ := by
  simp only [hasFiniteIntegral_iff_norm, edist_dist, dist_zero_right]

/--
theorem `hasFiniteIntegral_iff_ofReal` / 定理 `hasFiniteIntegral_iff_ofReal`

English:
theorem hasFiniteIntegral_iff_ofReal
  given: {f : α -> Real} (h : 0 <=ᵐ[μ] f)
  proof: by
  rw [hasFiniteIntegral_iff_enorm]; rw [lintegral_enorm_of_ae_nonneg h]

中文:
定理 hasFinite整数egral_iff_of实数
  条件: {f : α -> 实数} (h : 0 <=ᵐ[μ] f)
  证明: by
  rw [hasFiniteIntegral_iff_enorm]; rw [lintegral_enorm_of_ae_nonneg h]

Depends on / 依赖: hasFiniteIntegral_iff_enorm, lintegral_enorm_of_ae_nonneg
-/
theorem hasFiniteIntegral_iff_ofReal {f : α -> Real} (h : 0 <=ᵐ[μ] f) :
    HasFiniteIntegral f μ ↔ (∫⁻ a, ENNReal.ofReal (f a) ∂μ) < ∞ := by
  rw [hasFiniteIntegral_iff_enorm]; rw [lintegral_enorm_of_ae_nonneg h]

/--
theorem `hasFiniteIntegral_iff_ofNNReal` / 定理 `hasFiniteIntegral_iff_ofNNReal`

English:
theorem hasFiniteIntegral_iff_ofNNReal
  given: {f : α -> Real>=0}
  proof: by
  simp [hasFiniteIntegral_iff_norm]

中文:
定理 hasFinite整数egral_iff_ofNN实数
  条件: {f : α -> 实数>=0}
  证明: by
  simp [hasFiniteIntegral_iff_norm]

Depends on / 依赖: hasFiniteIntegral_iff_norm
-/
theorem hasFiniteIntegral_iff_ofNNReal {f : α -> Real>=0} :
    HasFiniteIntegral (fun x => (f x : Real)) μ ↔ (∫⁻ a, f a ∂μ) < ∞ := by
  simp [hasFiniteIntegral_iff_norm]

/--
theorem `HasFiniteIntegral.mono_enorm` / 定理 `HasFiniteIntegral.mono_enorm`

English:
theorem HasFiniteIntegral.mono_enorm
  statement: {f : α -> ε} {g : α -> ε'} (hg : HasFiniteIntegral g μ)
  proof: by
  simp only [hasFiniteIntegral_iff_enorm] at *
  calc
    (∫⁻ a, ‖f a‖ₑ ∂μ) <= ∫⁻ a : α, ‖g a‖ₑ ∂μ := lintegral_mono_ae h
    _ < ∞ := hg

中文:
定理 HasFinite整数egral.mono_enorm
  结论: {f : α -> ε} {g : α -> ε'} (hg : HasFinite整数egral g μ)
  证明: by
  simp only [hasFiniteIntegral_iff_enorm] at *
  calc
    (∫⁻ a, ‖f a‖ₑ ∂μ) <= ∫⁻ a : α, ‖g a‖ₑ ∂μ := lintegral_mono_ae h
    _ < ∞ := hg

Depends on / 依赖: hasFiniteIntegral_iff_enorm, lintegral_mono_ae
-/
theorem HasFiniteIntegral.mono_enorm {f : α -> ε} {g : α -> ε'} (hg : HasFiniteIntegral g μ)
    (h : forallᵐ a ∂μ, ‖f a‖ₑ <= ‖g a‖ₑ) : HasFiniteIntegral f μ := by
  simp only [hasFiniteIntegral_iff_enorm] at *
  calc
    (∫⁻ a, ‖f a‖ₑ ∂μ) <= ∫⁻ a : α, ‖g a‖ₑ ∂μ := lintegral_mono_ae h
    _ < ∞ := hg

/--
theorem `HasFiniteIntegral.mono` / 定理 `HasFiniteIntegral.mono`

English:
theorem HasFiniteIntegral.mono
  statement: {f : α -> β} {g : α -> γ} (hg : HasFiniteIntegral g μ)
  proof: hg.mono_enorm h.mono fun _x hx => enorm_le_iff_norm_le.mpr hx

中文:
定理 HasFinite整数egral.mono
  结论: {f : α -> β} {g : α -> γ} (hg : HasFinite整数egral g μ)
  证明: hg.mono_enorm h.mono fun _x hx => enorm_le_iff_norm_le.mpr hx

Depends on / 依赖: enorm_le_iff_norm_le, enorm_le_iff_norm_le.mpr, h.mono, hg.mono_enorm, mono_enorm
-/
theorem HasFiniteIntegral.mono {f : α -> β} {g : α -> γ} (hg : HasFiniteIntegral g μ)
    (h : forallᵐ a ∂μ, ‖f a‖ <= ‖g a‖) : HasFiniteIntegral f μ :=
hg.mono_enorm h.mono fun _x hx => enorm_le_iff_norm_le.mpr hx

/--
theorem `HasFiniteIntegral.mono_nonneg` / 定理 `HasFiniteIntegral.mono_nonneg`

English:
theorem HasFiniteIntegral.mono_nonneg
  statement: [Lattice β] [HasSolidNorm β] [AddLeftMono β] {f g : α -> β}
  proof: by
  refine HasFiniteIntegral.mono hg ?_
  filter_upwards [hnonneg, h] with a hn ha
  apply norm_le_norm_of_abs_le_abs
  rwa [abs_of_nonneg hn, abs_of_nonneg (hn.trans ha)]

中文:
定理 HasFinite整数egral.mono_nonneg
  结论: [格 β] [有Solid范数 β] [AddLeftMono β] {f g : α -> β}
  证明: by
  refine HasFiniteIntegral.mono hg ?_
  filter_upwards [hnonneg, h] with a hn ha
  apply norm_le_norm_of_abs_le_abs
  rwa [abs_of_nonneg hn, abs_of_nonneg (hn.trans ha)]

Depends on / 依赖: HasFiniteIntegral, HasFiniteIntegral.mono, abs_of_nonneg, filter_upwards, hn.trans, hnonneg, norm_le_norm_of_abs_le_abs
-/
theorem HasFiniteIntegral.mono_nonneg [Lattice β] [HasSolidNorm β] [AddLeftMono β] {f g : α -> β}
    (hg : HasFiniteIntegral g μ) (hnonneg : forallᵐ a ∂μ, 0 <= f a) (h : forallᵐ a ∂μ, f a <= g a) :
    HasFiniteIntegral f μ := by
  refine HasFiniteIntegral.mono hg ?_
  filter_upwards [hnonneg, h] with a hn ha
  apply norm_le_norm_of_abs_le_abs
  rwa [abs_of_nonneg hn, abs_of_nonneg (hn.trans ha)]

/--
theorem `HasFiniteIntegral.mono'_enorm` / 定理 `HasFiniteIntegral.mono'_enorm`

English:
theorem HasFiniteIntegral.mono'_enorm
  statement: {f : α -> ε} {g : α -> Real>=0∞} (hg : HasFiniteIntegral g μ)
  proof: hg.mono_enorm h.mono fun _x hx => le_trans hx le_rfl

中文:
定理 HasFinite整数egral.mono'_enorm
  结论: {f : α -> ε} {g : α -> 实数>=0∞} (hg : HasFinite整数egral g μ)
  证明: hg.mono_enorm h.mono fun _x hx => le_trans hx le_rfl

Depends on / 依赖: h.mono, hg.mono_enorm, le_rfl, le_trans, mono_enorm
-/
theorem HasFiniteIntegral.mono'_enorm {f : α -> ε} {g : α -> Real>=0∞} (hg : HasFiniteIntegral g μ)
    (h : forallᵐ a ∂μ, ‖f a‖ₑ <= g a) : HasFiniteIntegral f μ :=
hg.mono_enorm h.mono fun _x hx => le_trans hx le_rfl

/--
theorem `HasFiniteIntegral.mono'` / 定理 `HasFiniteIntegral.mono'`

English:
theorem HasFiniteIntegral.mono'
  statement: {f : α -> β} {g : α -> Real} (hg : HasFiniteIntegral g μ)
  proof: hg.mono h.mono fun _x hx => le_trans hx (le_abs_self _)

中文:
定理 HasFinite整数egral.mono'
  结论: {f : α -> β} {g : α -> 实数} (hg : HasFinite整数egral g μ)
  证明: hg.mono h.mono fun _x hx => le_trans hx (le_abs_self _)
-/
theorem HasFiniteIntegral.mono' {f : α -> β} {g : α -> Real} (hg : HasFiniteIntegral g μ)
    (h : forallᵐ a ∂μ, ‖f a‖ <= g a) : HasFiniteIntegral f μ :=
hg.mono h.mono fun _x hx => le_trans hx (le_abs_self _)

/--
theorem `HasFiniteIntegral.congr'_enorm` / 定理 `HasFiniteIntegral.congr'_enorm`

English:
theorem HasFiniteIntegral.congr'_enorm
  statement: {f : α -> ε} {g : α -> ε'} (hf : HasFiniteIntegral f μ)
  proof: hf.mono_enorm EventuallyEq.le EventuallyEq.symm h

中文:
定理 HasFinite整数egral.congr'_enorm
  结论: {f : α -> ε} {g : α -> ε'} (hf : HasFinite整数egral f μ)
  证明: hf.mono_enorm EventuallyEq.le EventuallyEq.symm h

Depends on / 依赖: EventuallyEq, EventuallyEq.le, EventuallyEq.symm, hf.mono_enorm, mono_enorm
-/
theorem HasFiniteIntegral.congr'_enorm {f : α -> ε} {g : α -> ε'} (hf : HasFiniteIntegral f μ)
    (h : forallᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : HasFiniteIntegral g μ :=
hf.mono_enorm EventuallyEq.le EventuallyEq.symm h

/--
theorem `HasFiniteIntegral.congr'` / 定理 `HasFiniteIntegral.congr'`

English:
theorem HasFiniteIntegral.congr'
  statement: {f : α -> β} {g : α -> γ} (hf : HasFiniteIntegral f μ)
  proof: hf.mono EventuallyEq.le EventuallyEq.symm h

中文:
定理 HasFinite整数egral.congr'
  结论: {f : α -> β} {g : α -> γ} (hf : HasFinite整数egral f μ)
  证明: hf.mono EventuallyEq.le EventuallyEq.symm h
-/
theorem HasFiniteIntegral.congr' {f : α -> β} {g : α -> γ} (hf : HasFiniteIntegral f μ)
    (h : forallᵐ a ∂μ, ‖f a‖ = ‖g a‖) : HasFiniteIntegral g μ :=
hf.mono EventuallyEq.le EventuallyEq.symm h

/--
theorem `hasFiniteIntegral_congr'_enorm` / 定理 `hasFiniteIntegral_congr'_enorm`

English:
theorem hasFiniteIntegral_congr'_enorm
  given: {f : α -> ε} {g : α -> ε'} (h : forallᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ)
  proof: ⟨fun hf => hf.congr'_enorm h, fun hg => hg.congr'_enorm EventuallyEq.symm h⟩

中文:
定理 hasFinite整数egral_congr'_enorm
  条件: {f : α -> ε} {g : α -> ε'} (h : 对任意ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ)
  证明: ⟨fun hf => hf.congr'_enorm h, fun hg => hg.congr'_enorm EventuallyEq.symm h⟩

Depends on / 依赖: EventuallyEq, EventuallyEq.symm, _enorm, hf.congr, hg.congr
-/
theorem hasFiniteIntegral_congr'_enorm {f : α -> ε} {g : α -> ε'} (h : forallᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) :
    HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ :=
⟨fun hf => hf.congr'_enorm h, fun hg => hg.congr'_enorm EventuallyEq.symm h⟩

/--
theorem `hasFiniteIntegral_congr'` / 定理 `hasFiniteIntegral_congr'`

English:
theorem hasFiniteIntegral_congr'
  given: {f : α -> β} {g : α -> γ} (h : forallᵐ a ∂μ, ‖f a‖ = ‖g a‖)
  proof: ⟨fun hf => hf.congr' h, fun hg => hg.congr' EventuallyEq.symm h⟩

中文:
定理 hasFinite整数egral_congr'
  条件: {f : α -> β} {g : α -> γ} (h : 对任意ᵐ a ∂μ, ‖f a‖ = ‖g a‖)
  证明: ⟨fun hf => hf.congr' h, fun hg => hg.congr' EventuallyEq.symm h⟩
-/
theorem hasFiniteIntegral_congr' {f : α -> β} {g : α -> γ} (h : forallᵐ a ∂μ, ‖f a‖ = ‖g a‖) :
    HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ :=
⟨fun hf => hf.congr' h, fun hg => hg.congr' EventuallyEq.symm h⟩

/--
theorem `HasFiniteIntegral.congr` / 定理 `HasFiniteIntegral.congr`

English:
theorem HasFiniteIntegral.congr
  given: {f g : α -> ε} (hf : HasFiniteIntegral f μ) (h : f =ᵐ[μ] g)
  proof: hf.congr'_enorm h.fun_comp enorm

中文:
定理 HasFinite整数egral.congr
  条件: {f g : α -> ε} (hf : HasFinite整数egral f μ) (h : f =ᵐ[μ] g)
  证明: hf.congr'_enorm h.fun_comp enorm

Depends on / 依赖: _enorm, fun_comp, h.fun_comp, hf.congr
-/
theorem HasFiniteIntegral.congr {f g : α -> ε} (hf : HasFiniteIntegral f μ) (h : f =ᵐ[μ] g) :
    HasFiniteIntegral g μ :=
hf.congr'_enorm h.fun_comp enorm

/--
theorem `hasFiniteIntegral_congr` / 定理 `hasFiniteIntegral_congr`

English:
theorem hasFiniteIntegral_congr
  given: {f g : α -> ε} (h : f =ᵐ[μ] g)
  proof: hasFiniteIntegral_congr'_enorm h.fun_comp enorm

中文:
定理 hasFinite整数egral_congr
  条件: {f g : α -> ε} (h : f =ᵐ[μ] g)
  证明: hasFiniteIntegral_congr'_enorm h.fun_comp enorm

Depends on / 依赖: _enorm, fun_comp, h.fun_comp, hasFiniteIntegral_congr
-/
theorem hasFiniteIntegral_congr {f g : α -> ε} (h : f =ᵐ[μ] g) :
    HasFiniteIntegral f μ ↔ HasFiniteIntegral g μ :=
hasFiniteIntegral_congr'_enorm h.fun_comp enorm

/--
theorem `hasFiniteIntegral_const_iff_enorm` / 定理 `hasFiniteIntegral_const_iff_enorm`

English:
theorem hasFiniteIntegral_const_iff_enorm
  given: {c : ε} (hc : ‖c‖ₑ != ∞)
  proof: by
  simpa [hasFiniteIntegral_iff_enorm, lt_top_iff_ne_top, ENNReal.mul_eq_top,
    or_iff_not_imp_left, isFiniteMeasure_iff] using fun h h' => (hc h').elim

中文:
定理 hasFinite整数egral_const_iff_enorm
  条件: {c : ε} (hc : ‖c‖ₑ != ∞)
  证明: by
  simpa [hasFiniteIntegral_iff_enorm, lt_top_iff_ne_top, ENNReal.mul_eq_top,
    or_iff_not_imp_left, isFiniteMeasure_iff] using fun h h' => (hc h').elim

Depends on / 依赖: ENNReal, ENNReal.mul_eq_top, hasFiniteIntegral_iff_enorm, isFiniteMeasure_iff, lt_top_iff_ne_top, mul_eq_top, or_iff_not_imp_left
-/
theorem hasFiniteIntegral_const_iff_enorm {c : ε} (hc : ‖c‖ₑ != ∞) :
    HasFiniteIntegral (fun _ : α => c) μ ↔ ‖c‖ₑ = 0 ∨ IsFiniteMeasure μ := by
  simpa [hasFiniteIntegral_iff_enorm, lt_top_iff_ne_top, ENNReal.mul_eq_top,
    or_iff_not_imp_left, isFiniteMeasure_iff] using fun h h' => (hc h').elim

/--
theorem `hasFiniteIntegral_const_iff` / 定理 `hasFiniteIntegral_const_iff`

English:
theorem hasFiniteIntegral_const_iff
  given: {c : β}
  proof: by
  simp [hasFiniteIntegral_const_iff_enorm enorm_ne_top]

中文:
定理 hasFinite整数egral_const_iff
  条件: {c : β}
  证明: by
  simp [hasFiniteIntegral_const_iff_enorm enorm_ne_top]

Depends on / 依赖: enorm_ne_top, hasFiniteIntegral_const_iff_enorm
-/
theorem hasFiniteIntegral_const_iff {c : β} :
    HasFiniteIntegral (fun _ : α => c) μ ↔ c = 0 ∨ IsFiniteMeasure μ := by
  simp [hasFiniteIntegral_const_iff_enorm enorm_ne_top]

/--
lemma `hasFiniteIntegral_const_iff_isFiniteMeasure_enorm` / 引理 `hasFiniteIntegral_const_iff_isFiniteMeasure_enorm`

English:
lemma hasFiniteIntegral_const_iff_isFiniteMeasure_enorm
  given: {c : ε} (hc : ‖c‖ₑ != 0) (hc' : ‖c‖ₑ != ∞)
  proof: by
  simp [hasFiniteIntegral_const_iff_enorm hc', hc, isFiniteMeasure_iff]

中文:
引理 hasFinite整数egral_const_iff_isFiniteMeasure_enorm
  条件: {c : ε} (hc : ‖c‖ₑ != 0) (hc' : ‖c‖ₑ != ∞)
  证明: by
  simp [hasFiniteIntegral_const_iff_enorm hc', hc, isFiniteMeasure_iff]

Depends on / 依赖: hasFiniteIntegral_const_iff_enorm, isFiniteMeasure_iff
-/
lemma hasFiniteIntegral_const_iff_isFiniteMeasure_enorm {c : ε} (hc : ‖c‖ₑ != 0) (hc' : ‖c‖ₑ != ∞) :
    HasFiniteIntegral (fun _ => c) μ ↔ IsFiniteMeasure μ := by
  simp [hasFiniteIntegral_const_iff_enorm hc', hc, isFiniteMeasure_iff]

/--
lemma `hasFiniteIntegral_const_iff_isFiniteMeasure` / 引理 `hasFiniteIntegral_const_iff_isFiniteMeasure`

English:
lemma hasFiniteIntegral_const_iff_isFiniteMeasure
  given: {c : β} (hc : c != 0)
  proof: hasFiniteIntegral_const_iff_isFiniteMeasure_enorm (enorm_ne_zero.mpr hc) enorm_ne_top

@[fun_prop]

中文:
引理 hasFinite整数egral_const_iff_isFiniteMeasure
  条件: {c : β} (hc : c != 0)
  证明: hasFiniteIntegral_const_iff_isFiniteMeasure_enorm (enorm_ne_zero.mpr hc) enorm_ne_top

@[fun_prop]

Depends on / 依赖: enorm_ne_top, enorm_ne_zero, enorm_ne_zero.mpr, hasFiniteIntegral_const_iff_isFiniteMeasure_enorm
-/
lemma hasFiniteIntegral_const_iff_isFiniteMeasure {c : β} (hc : c != 0) :
    HasFiniteIntegral (fun _ => c) μ ↔ IsFiniteMeasure μ :=
  hasFiniteIntegral_const_iff_isFiniteMeasure_enorm (enorm_ne_zero.mpr hc) enorm_ne_top

@[fun_prop]
/--
theorem `hasFiniteIntegral_const_enorm` / 定理 `hasFiniteIntegral_const_enorm`

English:
theorem hasFiniteIntegral_const_enorm
  given: [IsFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞)
  proof: (hasFiniteIntegral_const_iff_enorm hc).2 .inr ‹_›

@[fun_prop]

中文:
定理 hasFinite整数egral_const_enorm
  条件: [是有限测度 μ] {c : ε} (hc : ‖c‖ₑ != ∞)
  证明: (hasFiniteIntegral_const_iff_enorm hc).2 .inr ‹_›

@[fun_prop]

Depends on / 依赖: hasFiniteIntegral_const_iff_enorm
-/
theorem hasFiniteIntegral_const_enorm [IsFiniteMeasure μ] {c : ε} (hc : ‖c‖ₑ != ∞) :
    HasFiniteIntegral (fun _ : α => c) μ :=
(hasFiniteIntegral_const_iff_enorm hc).2 .inr ‹_›

@[fun_prop]
/--
theorem `hasFiniteIntegral_const` / 定理 `hasFiniteIntegral_const`

English:
theorem hasFiniteIntegral_const
  given: [IsFiniteMeasure μ] (c : β)
  proof: hasFiniteIntegral_const_iff.2 .inr ‹_›

中文:
定理 hasFinite整数egral_const
  条件: [是有限测度 μ] (c : β)
  证明: hasFiniteIntegral_const_iff.2 .inr ‹_›

Depends on / 依赖: hasFiniteIntegral_const_iff
-/
theorem hasFiniteIntegral_const [IsFiniteMeasure μ] (c : β) :
    HasFiniteIntegral (fun _ : α => c) μ :=
hasFiniteIntegral_const_iff.2 .inr ‹_›

/--
theorem `HasFiniteIntegral.of_mem_Icc_of_ne_top` / 定理 `HasFiniteIntegral.of_mem_Icc_of_ne_top`

English:
theorem HasFiniteIntegral.of_mem_Icc_of_ne_top
  statement: [IsFiniteMeasure μ]
  proof: by
  have : ‖max ‖a‖ₑ ‖b‖ₑ‖ₑ != ⊤ := by simp [ha, hb]
  apply (hasFiniteIntegral_const_enorm this (μ := μ)).mono'_enorm
  filter_upwards [h.mono fun ω h => h.1, h.mono fun ω h => h.2] with ω h₁ h₂ using by simp [h₂]

中文:
定理 HasFinite整数egral.of_mem_Icc_of_ne_top
  结论: [是有限测度 μ]
  证明: by
  have : ‖max ‖a‖ₑ ‖b‖ₑ‖ₑ != ⊤ := by simp [ha, hb]
  apply (hasFiniteIntegral_const_enorm this (μ := μ)).mono'_enorm
  filter_upwards [h.mono fun ω h => h.1, h.mono fun ω h => h.2] with ω h₁ h₂ using by simp [h₂]

Depends on / 依赖: _enorm, filter_upwards, h.mono, hasFiniteIntegral_const_enorm
-/
theorem HasFiniteIntegral.of_mem_Icc_of_ne_top [IsFiniteMeasure μ]
    {a b : Real>=0∞} (ha : a != ⊤) (hb : b != ⊤) {X : α -> Real>=0∞} (h : forallᵐ ω ∂μ, X ω in Set.Icc a b) :
    HasFiniteIntegral X μ := by
  have : ‖max ‖a‖ₑ ‖b‖ₑ‖ₑ != ⊤ := by simp [ha, hb]
  apply (hasFiniteIntegral_const_enorm this (μ := μ)).mono'_enorm
  filter_upwards [h.mono fun ω h => h.1, h.mono fun ω h => h.2] with ω h₁ h₂ using by simp [h₂]

/--
theorem `HasFiniteIntegral.of_mem_Icc` / 定理 `HasFiniteIntegral.of_mem_Icc`

English:
theorem HasFiniteIntegral.of_mem_Icc
  statement: [IsFiniteMeasure μ] (a b : Real) {X : α -> Real}
  proof: by
  apply (hasFiniteIntegral_const (max ‖a‖ ‖b‖)).mono'
  filter_upwards [h.mono fun ω h => h.1, h.mono fun ω h => h.2] with ω using abs_le_max_abs_abs

中文:
定理 HasFinite整数egral.of_mem_Icc
  结论: [是有限测度 μ] (a b : 实数) {X : α -> 实数}
  证明: by
  apply (hasFiniteIntegral_const (max ‖a‖ ‖b‖)).mono'
  filter_upwards [h.mono fun ω h => h.1, h.mono fun ω h => h.2] with ω using abs_le_max_abs_abs

Depends on / 依赖: abs_le_max_abs_abs, filter_upwards, h.mono, hasFiniteIntegral_const
-/
theorem HasFiniteIntegral.of_mem_Icc [IsFiniteMeasure μ] (a b : Real) {X : α -> Real}
    (h : forallᵐ ω ∂μ, X ω in Set.Icc a b) :
    HasFiniteIntegral X μ := by
  apply (hasFiniteIntegral_const (max ‖a‖ ‖b‖)).mono'
  filter_upwards [h.mono fun ω h => h.1, h.mono fun ω h => h.2] with ω using abs_le_max_abs_abs

/--
theorem `HasFiniteIntegral.of_bounded_enorm` / 定理 `HasFiniteIntegral.of_bounded_enorm`

English:
theorem HasFiniteIntegral.of_bounded_enorm
  statement: [IsFiniteMeasure μ] {f : α -> ε} {C : Real>=0∞}
  proof: (hasFiniteIntegral_const_enorm hC').mono'_enorm hC

中文:
定理 HasFinite整数egral.of_bounded_enorm
  结论: [是有限测度 μ] {f : α -> ε} {C : 实数>=0∞}
  证明: (hasFiniteIntegral_const_enorm hC').mono'_enorm hC

Depends on / 依赖: HasFiniteIntegral, _enorm, finiteness, hasFiniteIntegral_const_enorm
-/
theorem HasFiniteIntegral.of_bounded_enorm [IsFiniteMeasure μ] {f : α -> ε} {C : Real>=0∞}
    (hC' : ‖C‖ₑ != ∞ := by finiteness) (hC : forallᵐ a ∂μ, ‖f a‖ₑ <= C) : HasFiniteIntegral f μ :=
  (hasFiniteIntegral_const_enorm hC').mono'_enorm hC

/--
theorem `HasFiniteIntegral.of_bounded` / 定理 `HasFiniteIntegral.of_bounded`

English:
theorem HasFiniteIntegral.of_bounded
  statement: [IsFiniteMeasure μ] {f : α -> β} {C : Real}
  proof: (hasFiniteIntegral_const C).mono' hC

中文:
定理 HasFinite整数egral.of_bounded
  结论: [是有限测度 μ] {f : α -> β} {C : 实数}
  证明: (hasFiniteIntegral_const C).mono' hC

Depends on / 依赖: hasFiniteIntegral_const
-/
theorem HasFiniteIntegral.of_bounded [IsFiniteMeasure μ] {f : α -> β} {C : Real}
    (hC : forallᵐ a ∂μ, ‖f a‖ <= C) : HasFiniteIntegral f μ :=
  (hasFiniteIntegral_const C).mono' hC

-- TODO: generalise this to f with codomain ε
-- requires generalising `norm_le_pi_norm` and friends to enorms
@[simp]
/--
theorem `HasFiniteIntegral.of_finite` / 定理 `HasFiniteIntegral.of_finite`

English:
theorem HasFiniteIntegral.of_finite
  given: [Finite α] [IsFiniteMeasure μ] {f : α -> β}
  proof: let ⟨_⟩ := nonempty_fintype α
.of_bounded ae_of_all μ norm_le_pi_norm f

中文:
定理 HasFinite整数egral.of_finite
  条件: [有限 α] [是有限测度 μ] {f : α -> β}
  证明: let ⟨_⟩ := nonempty_fintype α
.of_bounded ae_of_all μ norm_le_pi_norm f

Depends on / 依赖: ae_of_all, nonempty_fintype, norm_le_pi_norm, of_bounded
-/
theorem HasFiniteIntegral.of_finite [Finite α] [IsFiniteMeasure μ] {f : α -> β} :
    HasFiniteIntegral f μ :=
  let ⟨_⟩ := nonempty_fintype α
.of_bounded ae_of_all μ norm_le_pi_norm f

/--
theorem `HasFiniteIntegral.mono_measure` / 定理 `HasFiniteIntegral.mono_measure`

English:
theorem HasFiniteIntegral.mono_measure
  given: {f : α -> ε} (h : HasFiniteIntegral f ν) (hμ : μ <= ν)
  proof: lt_of_le_of_lt (lintegral_mono' hμ le_rfl) h

@[fun_prop]

中文:
定理 HasFinite整数egral.mono_measure
  条件: {f : α -> ε} (h : HasFinite整数egral f ν) (hμ : μ <= ν)
  证明: lt_of_le_of_lt (lintegral_mono' hμ le_rfl) h

@[fun_prop]

Depends on / 依赖: le_rfl, lintegral_mono, lt_of_le_of_lt
-/
theorem HasFiniteIntegral.mono_measure {f : α -> ε} (h : HasFiniteIntegral f ν) (hμ : μ <= ν) :
    HasFiniteIntegral f μ :=
  lt_of_le_of_lt (lintegral_mono' hμ le_rfl) h

@[fun_prop]
/--
theorem `HasFiniteIntegral.add_measure` / 定理 `HasFiniteIntegral.add_measure`

English:
theorem HasFiniteIntegral.add_measure
  statement: {f : α -> ε} (hμ : HasFiniteIntegral f μ)
  proof: by
  simp only [HasFiniteIntegral, lintegral_add_measure] at *
  exact add_lt_top.2 ⟨hμ, hν⟩

中文:
定理 HasFinite整数egral.add_measure
  结论: {f : α -> ε} (hμ : HasFinite整数egral f μ)
  证明: by
  simp only [HasFiniteIntegral, lintegral_add_measure] at *
  exact add_lt_top.2 ⟨hμ, hν⟩

Depends on / 依赖: HasFiniteIntegral, add_lt_top, lintegral_add_measure
-/
theorem HasFiniteIntegral.add_measure {f : α -> ε} (hμ : HasFiniteIntegral f μ)
    (hν : HasFiniteIntegral f ν) : HasFiniteIntegral f (μ + ν) := by
  simp only [HasFiniteIntegral, lintegral_add_measure] at *
  exact add_lt_top.2 ⟨hμ, hν⟩

/--
theorem `HasFiniteIntegral.left_of_add_measure` / 定理 `HasFiniteIntegral.left_of_add_measure`

English:
theorem HasFiniteIntegral.left_of_add_measure
  given: {f : α -> ε} (h : HasFiniteIntegral f (μ + ν))
  proof: h.mono_measure Measure.le_add_right le_rfl

中文:
定理 HasFinite整数egral.left_of_add_measure
  条件: {f : α -> ε} (h : HasFinite整数egral f (μ + ν))
  证明: h.mono_measure Measure.le_add_right le_rfl

Depends on / 依赖: Measure, Measure.le_add_right, h.mono_measure, le_add_right, le_rfl, mono_measure
-/
theorem HasFiniteIntegral.left_of_add_measure {f : α -> ε} (h : HasFiniteIntegral f (μ + ν)) :
    HasFiniteIntegral f μ :=
h.mono_measure Measure.le_add_right le_rfl

/--
theorem `HasFiniteIntegral.right_of_add_measure` / 定理 `HasFiniteIntegral.right_of_add_measure`

English:
theorem HasFiniteIntegral.right_of_add_measure
  given: {f : α -> ε} (h : HasFiniteIntegral f (μ + ν))
  proof: h.mono_measure Measure.le_add_left le_rfl

@[simp]

中文:
定理 HasFinite整数egral.right_of_add_measure
  条件: {f : α -> ε} (h : HasFinite整数egral f (μ + ν))
  证明: h.mono_measure Measure.le_add_left le_rfl

@[simp]

Depends on / 依赖: Measure, Measure.le_add_left, h.mono_measure, le_add_left, le_rfl, mono_measure
-/
theorem HasFiniteIntegral.right_of_add_measure {f : α -> ε} (h : HasFiniteIntegral f (μ + ν)) :
    HasFiniteIntegral f ν :=
h.mono_measure Measure.le_add_left le_rfl

@[simp]
/--
theorem `hasFiniteIntegral_add_measure` / 定理 `hasFiniteIntegral_add_measure`

English:
theorem hasFiniteIntegral_add_measure
  given: {f : α -> ε}
  proof: ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩

中文:
定理 hasFinite整数egral_add_measure
  条件: {f : α -> ε}
  证明: ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩

Depends on / 依赖: add_measure, h.left_of_add_measure, h.right_of_add_measure, left_of_add_measure, right_of_add_measure
-/
theorem hasFiniteIntegral_add_measure {f : α -> ε} :
    HasFiniteIntegral f (μ + ν) ↔ HasFiniteIntegral f μ ∧ HasFiniteIntegral f ν :=
  ⟨fun h => ⟨h.left_of_add_measure, h.right_of_add_measure⟩, fun h => h.1.add_measure h.2⟩

/--
theorem `HasFiniteIntegral.smul_measure` / 定理 `HasFiniteIntegral.smul_measure`

English:
theorem HasFiniteIntegral.smul_measure
  statement: {f : α -> ε} (h : HasFiniteIntegral f μ) {c : Real>=0∞}
  proof: by
  simp only [HasFiniteIntegral, lintegral_smul_measure] at *
  exact mul_lt_top hc.lt_top h

@[fun_prop, simp]

中文:
定理 HasFinite整数egral.smul_measure
  结论: {f : α -> ε} (h : HasFinite整数egral f μ) {c : 实数>=0∞}
  证明: by
  simp only [HasFiniteIntegral, lintegral_smul_measure] at *
  exact mul_lt_top hc.lt_top h

@[fun_prop, simp]

Depends on / 依赖: HasFiniteIntegral, hc.lt_top, lintegral_smul_measure, lt_top, mul_lt_top
-/
theorem HasFiniteIntegral.smul_measure {f : α -> ε} (h : HasFiniteIntegral f μ) {c : Real>=0∞}
    (hc : c != ∞) : HasFiniteIntegral f (c • μ) := by
  simp only [HasFiniteIntegral, lintegral_smul_measure] at *
  exact mul_lt_top hc.lt_top h

@[fun_prop, simp]
/--
theorem `hasFiniteIntegral_zero_measure` / 定理 `hasFiniteIntegral_zero_measure`

English:
theorem hasFiniteIntegral_zero_measure
  given: {m : MeasurableSpace α} (f : α -> ε)
  proof: by
  simp only [HasFiniteIntegral, lintegral_zero_measure, zero_lt_top]

中文:
定理 hasFinite整数egral_zero_measure
  条件: {m : 可测空间 α} (f : α -> ε)
  证明: by
  simp only [HasFiniteIntegral, lintegral_zero_measure, zero_lt_top]

Depends on / 依赖: HasFiniteIntegral, lintegral_zero_measure, zero_lt_top
-/
theorem hasFiniteIntegral_zero_measure {m : MeasurableSpace α} (f : α -> ε) :
    HasFiniteIntegral f (0 : Measure α) := by
  simp only [HasFiniteIntegral, lintegral_zero_measure, zero_lt_top]

variable (α μ) in
@[to_fun (attr := fun_prop, simp) hasFiniteIntegral_fun_zero]
/--
theorem `hasFiniteIntegral_zero` / 定理 `hasFiniteIntegral_zero`

English:
theorem hasFiniteIntegral_zero
  given: {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  proof: by
  simp [hasFiniteIntegral_iff_enorm]

@[fun_prop]

中文:
定理 hasFinite整数egral_zero
  条件: {ε : 类型} [拓扑空间 ε] [ESeminormedAdd幺半群 ε]
  证明: by
  simp [hasFiniteIntegral_iff_enorm]

@[fun_prop]

Depends on / 依赖: hasFiniteIntegral_iff_enorm
-/
theorem hasFiniteIntegral_zero {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] :
    HasFiniteIntegral (0 : α -> ε) μ := by
  simp [hasFiniteIntegral_iff_enorm]

@[fun_prop]
/--
theorem `HasFiniteIntegral.neg` / 定理 `HasFiniteIntegral.neg`

English:
theorem HasFiniteIntegral.neg
  given: {f : α -> β} (hfi : HasFiniteIntegral f μ)
  proof: by simpa [hasFiniteIntegral_iff_enorm] using hfi

@[simp]

中文:
定理 HasFinite整数egral.neg
  条件: {f : α -> β} (hfi : HasFinite整数egral f μ)
  证明: by simpa [hasFiniteIntegral_iff_enorm] using hfi

@[simp]

Depends on / 依赖: hasFiniteIntegral_iff_enorm
-/
theorem HasFiniteIntegral.neg {f : α -> β} (hfi : HasFiniteIntegral f μ) :
    HasFiniteIntegral (-f) μ := by simpa [hasFiniteIntegral_iff_enorm] using hfi

@[simp]
/--
theorem `hasFiniteIntegral_neg_iff` / 定理 `hasFiniteIntegral_neg_iff`

English:
theorem hasFiniteIntegral_neg_iff
  given: {f : α -> β}
  statement: HasFiniteIntegral (-f) μ ↔ HasFiniteIntegral f μ
  proof: ⟨fun h => neg_neg f ▸ h.neg, HasFiniteIntegral.neg⟩

@[fun_prop]

中文:
定理 hasFinite整数egral_neg_iff
  条件: {f : α -> β}
  结论: HasFinite整数egral (-f) μ ↔ HasFinite整数egral f μ
  证明: ⟨fun h => neg_neg f ▸ h.neg, HasFiniteIntegral.neg⟩

@[fun_prop]

Depends on / 依赖: HasFiniteIntegral, HasFiniteIntegral.neg, h.neg, neg_neg
-/
theorem hasFiniteIntegral_neg_iff {f : α -> β} : HasFiniteIntegral (-f) μ ↔ HasFiniteIntegral f μ :=
  ⟨fun h => neg_neg f ▸ h.neg, HasFiniteIntegral.neg⟩

@[fun_prop]
/--
theorem `HasFiniteIntegral.enorm` / 定理 `HasFiniteIntegral.enorm`

English:
theorem HasFiniteIntegral.enorm
  given: {f : α -> ε} (hfi : HasFiniteIntegral f μ)
  proof: by simpa [hasFiniteIntegral_iff_enorm] using hfi

@[fun_prop]

中文:
定理 HasFinite整数egral.enorm
  条件: {f : α -> ε} (hfi : HasFinite整数egral f μ)
  证明: by simpa [hasFiniteIntegral_iff_enorm] using hfi

@[fun_prop]

Depends on / 依赖: hasFiniteIntegral_iff_enorm
-/
theorem HasFiniteIntegral.enorm {f : α -> ε} (hfi : HasFiniteIntegral f μ) :
    HasFiniteIntegral (‖f ·‖ₑ) μ := by simpa [hasFiniteIntegral_iff_enorm] using hfi

@[fun_prop]
/--
theorem `HasFiniteIntegral.norm` / 定理 `HasFiniteIntegral.norm`

English:
theorem HasFiniteIntegral.norm
  given: {f : α -> β} (hfi : HasFiniteIntegral f μ)
  proof: by simpa [hasFiniteIntegral_iff_enorm] using hfi

中文:
定理 HasFinite整数egral.norm
  条件: {f : α -> β} (hfi : HasFinite整数egral f μ)
  证明: by simpa [hasFiniteIntegral_iff_enorm] using hfi

Depends on / 依赖: hasFiniteIntegral_iff_enorm
-/
theorem HasFiniteIntegral.norm {f : α -> β} (hfi : HasFiniteIntegral f μ) :
    HasFiniteIntegral (fun a => ‖f a‖) μ := by simpa [hasFiniteIntegral_iff_enorm] using hfi

/--
theorem `hasFiniteIntegral_enorm_iff` / 定理 `hasFiniteIntegral_enorm_iff`

English:
theorem hasFiniteIntegral_enorm_iff
  given: (f : α -> ε)
  proof: hasFiniteIntegral_congr'_enorm Eventually.of_forall fun x => enorm_enorm (f x)

中文:
定理 hasFinite整数egral_enorm_iff
  条件: (f : α -> ε)
  证明: hasFiniteIntegral_congr'_enorm Eventually.of_forall fun x => enorm_enorm (f x)

Depends on / 依赖: Eventually, Eventually.of_forall, _enorm, enorm_enorm, hasFiniteIntegral_congr, of_forall
-/
theorem hasFiniteIntegral_enorm_iff (f : α -> ε) :
    HasFiniteIntegral (‖f ·‖ₑ) μ ↔ HasFiniteIntegral f μ :=
hasFiniteIntegral_congr'_enorm Eventually.of_forall fun x => enorm_enorm (f x)

/--
theorem `hasFiniteIntegral_norm_iff` / 定理 `hasFiniteIntegral_norm_iff`

English:
theorem hasFiniteIntegral_norm_iff
  given: (f : α -> β)
  proof: hasFiniteIntegral_congr' Eventually.of_forall fun x => norm_norm (f x)

中文:
定理 hasFinite整数egral_norm_iff
  条件: (f : α -> β)
  证明: hasFiniteIntegral_congr' Eventually.of_forall fun x => norm_norm (f x)

Depends on / 依赖: Eventually, Eventually.of_forall, hasFiniteIntegral_congr, norm_norm, of_forall
-/
theorem hasFiniteIntegral_norm_iff (f : α -> β) :
    HasFiniteIntegral (fun a => ‖f a‖) μ ↔ HasFiniteIntegral f μ :=
hasFiniteIntegral_congr' Eventually.of_forall fun x => norm_norm (f x)

/--
theorem `HasFiniteIntegral.of_subsingleton` / 定理 `HasFiniteIntegral.of_subsingleton`

English:
theorem HasFiniteIntegral.of_subsingleton
  given: [Subsingleton α] [IsFiniteMeasure μ] {f : α -> β}
  proof: .of_finite

中文:
定理 HasFinite整数egral.of_subsingleton
  条件: [子单例 α] [是有限测度 μ] {f : α -> β}
  证明: .of_finite

Depends on / 依赖: of_finite
-/
theorem HasFiniteIntegral.of_subsingleton [Subsingleton α] [IsFiniteMeasure μ] {f : α -> β} :
    HasFiniteIntegral f μ :=
  .of_finite

/--
theorem `HasFiniteIntegral.of_isEmpty` / 定理 `HasFiniteIntegral.of_isEmpty`

English:
theorem HasFiniteIntegral.of_isEmpty
  given: [IsEmpty α] {f : α -> β}
  proof: .of_finite

@[simp]

中文:
定理 HasFinite整数egral.of_isEmpty
  条件: [是空 α] {f : α -> β}
  证明: .of_finite

@[simp]

Depends on / 依赖: of_finite
-/
theorem HasFiniteIntegral.of_isEmpty [IsEmpty α] {f : α -> β} :
    HasFiniteIntegral f μ :=
  .of_finite

@[simp]
/--
theorem `HasFiniteIntegral.of_subsingleton_codomain` / 定理 `HasFiniteIntegral.of_subsingleton_codomain`

English:
theorem HasFiniteIntegral.of_subsingleton_codomain
  proof: .congr .of_forall fun _ => Subsingleton.elim _ _ hasFiniteIntegral_zero _ _

中文:
定理 HasFinite整数egral.of_subsingleton_codomain
  证明: .congr .of_forall fun _ => Subsingleton.elim _ _ hasFiniteIntegral_zero _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim, hasFiniteIntegral_zero, of_forall
-/
theorem HasFiniteIntegral.of_subsingleton_codomain
    {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] [Subsingleton ε] {f : α -> ε} :
    HasFiniteIntegral f μ :=
.congr .of_forall fun _ => Subsingleton.elim _ _ hasFiniteIntegral_zero _ _

/--
theorem `hasFiniteIntegral_toReal_of_lintegral_ne_top` / 定理 `hasFiniteIntegral_toReal_of_lintegral_ne_top`

English:
theorem hasFiniteIntegral_toReal_of_lintegral_ne_top
  given: {f : α -> Real>=0∞} (hf : ∫⁻ x, f x ∂μ != ∞)
  proof: by
  have h x : ‖(f x).toReal‖ₑ = .ofReal (f x).toReal := by
    rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg]
  simp_rw [hasFiniteIntegral_iff_enorm, h]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) (lt_top_iff_ne_top.2 hf)
  by_cases hfx : f x = ∞
  · simp [hfx]
  · lift f x to Real>=0 us

中文:
定理 hasFinite整数egral_to实数_of_lintegral_ne_top
  条件: {f : α -> 实数>=0∞} (hf : ∫⁻ x, f x ∂μ != ∞)
  证明: by
  have h x : ‖(f x).toReal‖ₑ = .ofReal (f x).toReal := by
    rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg]
  simp_rw [hasFiniteIntegral_iff_enorm, h]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) (lt_top_iff_ne_top.2 hf)
  by_cases hfx : f x = ∞
  · simp [hfx]
  · lift f x to Real>=0 us

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, Real.enorm_of_nonneg, enorm_of_nonneg, hasFiniteIntegral_iff_enorm, lintegral_mono, lt_of_le_of_lt, lt_top_iff_ne_top, ofReal, simp_rw, toReal, toReal_nonneg
-/
theorem hasFiniteIntegral_toReal_of_lintegral_ne_top {f : α -> Real>=0∞} (hf : ∫⁻ x, f x ∂μ != ∞) :
    HasFiniteIntegral (fun x => (f x).toReal) μ := by
  have h x : ‖(f x).toReal‖ₑ = .ofReal (f x).toReal := by
    rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg]
  simp_rw [hasFiniteIntegral_iff_enorm, h]
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) (lt_top_iff_ne_top.2 hf)
  by_cases hfx : f x = ∞
  · simp [hfx]
  · lift f x to Real>=0 using hfx with fx h
    simp

/--
lemma `hasFiniteIntegral_toReal_iff` / 引理 `hasFiniteIntegral_toReal_iff`

English:
lemma hasFiniteIntegral_toReal_iff
  given: {f : α -> Real>=0∞} (hf : forallᵐ x ∂μ, f x != ∞)
  proof: by
  have : forallᵐ x ∂μ, .ofReal (f x).toReal = f x := by filter_upwards [hf] with x hx; simp [hx]
  simp [hasFiniteIntegral_iff_enorm, Real.enorm_of_nonneg ENNReal.toReal_nonneg,
    lintegral_congr_ae this, lt_top_iff_ne_top]

中文:
引理 hasFinite整数egral_to实数_iff
  条件: {f : α -> 实数>=0∞} (hf : 对任意ᵐ x ∂μ, f x != ∞)
  证明: by
  have : forallᵐ x ∂μ, .ofReal (f x).toReal = f x := by filter_upwards [hf] with x hx; simp [hx]
  simp [hasFiniteIntegral_iff_enorm, Real.enorm_of_nonneg ENNReal.toReal_nonneg,
    lintegral_congr_ae this, lt_top_iff_ne_top]

Depends on / 依赖: ENNReal, ENNReal.toReal_nonneg, Real.enorm_of_nonneg, enorm_of_nonneg, filter_upwards, hasFiniteIntegral_iff_enorm, lintegral_congr_ae, lt_top_iff_ne_top, ofReal, toReal, toReal_nonneg
-/
lemma hasFiniteIntegral_toReal_iff {f : α -> Real>=0∞} (hf : forallᵐ x ∂μ, f x != ∞) :
    HasFiniteIntegral (fun x => (f x).toReal) μ ↔ ∫⁻ x, f x ∂μ != ∞ := by
  have : forallᵐ x ∂μ, .ofReal (f x).toReal = f x := by filter_upwards [hf] with x hx; simp [hx]
  simp [hasFiniteIntegral_iff_enorm, Real.enorm_of_nonneg ENNReal.toReal_nonneg,
    lintegral_congr_ae this, lt_top_iff_ne_top]

/--
theorem `isFiniteMeasure_withDensity_ofReal` / 定理 `isFiniteMeasure_withDensity_ofReal`

English:
theorem isFiniteMeasure_withDensity_ofReal
  given: {f : α -> Real} (hfi : HasFiniteIntegral f μ)
  proof: by
  refine isFiniteMeasure_withDensity ((lintegral_mono fun x => ?_).trans_lt hfi).ne
  exact Real.ofReal_le_enorm (f x)

中文:
定理 isFiniteMeasure_withDensity_of实数
  条件: {f : α -> 实数} (hfi : HasFinite整数egral f μ)
  证明: by
  refine isFiniteMeasure_withDensity ((lintegral_mono fun x => ?_).trans_lt hfi).ne
  exact Real.ofReal_le_enorm (f x)

Depends on / 依赖: Real.ofReal_le_enorm, isFiniteMeasure_withDensity, lintegral_mono, ofReal_le_enorm, trans_lt
-/
theorem isFiniteMeasure_withDensity_ofReal {f : α -> Real} (hfi : HasFiniteIntegral f μ) :
    IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal <| f x) := by
  refine isFiniteMeasure_withDensity ((lintegral_mono fun x => ?_).trans_lt hfi).ne
  exact Real.ofReal_le_enorm (f x)

section DominatedConvergence

variable {F : Nat -> α -> β} {f : α -> β} {bound : α -> Real}
  {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  {F' : Nat -> α -> ε} {f' : α -> ε} {bound' : α -> Real>=0∞}

/--
theorem `all_ae_norm_ofReal_F_le_bound` / 定理 `all_ae_norm_ofReal_F_le_bound`

English:
theorem all_ae_norm_ofReal_F_le_bound
  given: (h : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound a)
  proof: fun n =>
  (h n).mono fun _ h => ENNReal.ofReal_le_ofReal h

@[deprecated (since := "2026-01-26")] alias
all_ae_ofReal_F_le_bound := all_ae_norm_ofReal_F_le_bound

中文:
定理 all_ae_norm_of实数_F_le_bound
  条件: (h : 对任意 n, 对任意ᵐ a ∂μ, ‖F n a‖ <= bound a)
  证明: fun n =>
  (h n).mono fun _ h => ENNReal.ofReal_le_ofReal h

@[deprecated (since := "2026-01-26")] alias
all_ae_ofReal_F_le_bound := all_ae_norm_ofReal_F_le_bound
-/
theorem all_ae_norm_ofReal_F_le_bound (h : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound a) :
    forall n, forallᵐ a ∂μ, ENNReal.ofReal ‖F n a‖ <= ENNReal.ofReal (bound a) := fun n =>
  (h n).mono fun _ h => ENNReal.ofReal_le_ofReal h

@[deprecated (since := "2026-01-26")] alias
all_ae_ofReal_F_le_bound := all_ae_norm_ofReal_F_le_bound

/--
theorem `ae_tendsto_enorm` / 定理 `ae_tendsto_enorm`

English:
theorem ae_tendsto_enorm
  given: (h : forallᵐ a ∂μ, Tendsto (fun n => F' n a) atTop <| 𝓝 <| f' a)
  proof: h.mono fun _ h => Tendsto.comp (Continuous.tendsto continuous_enorm _) h

中文:
定理 ae_tendsto_enorm
  条件: (h : 对任意ᵐ a ∂μ, 收敛 (fun n => F' n a) atTop <| 𝓝 <| f' a)
  证明: h.mono fun _ h => Tendsto.comp (Continuous.tendsto continuous_enorm _) h

Depends on / 依赖: Continuous, Continuous.tendsto, Tendsto, Tendsto.comp, continuous_enorm, h.mono, tendsto
-/
theorem ae_tendsto_enorm (h : forallᵐ a ∂μ, Tendsto (fun n => F' n a) atTop <| 𝓝 <| f' a) :
forallᵐ a ∂μ, Tendsto (fun n => ‖F' n a‖ₑ) atTop 𝓝 ‖f' a‖ₑ :=
  h.mono fun _ h => Tendsto.comp (Continuous.tendsto continuous_enorm _) h

/--
theorem `ae_tendsto_ofReal_norm` / 定理 `ae_tendsto_ofReal_norm`

English:
theorem ae_tendsto_ofReal_norm
  given: (h : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop <| 𝓝 <| f a)
  proof: by
  convert! ae_tendsto_enorm h <;> simp

@[deprecated (since := "2026-01-26")] alias all_ae_tendsto_ofReal_norm := ae_tendsto_ofReal_norm

中文:
定理 ae_tendsto_of实数_norm
  条件: (h : 对任意ᵐ a ∂μ, 收敛 (fun n => F n a) atTop <| 𝓝 <| f a)
  证明: by
  convert! ae_tendsto_enorm h <;> simp

@[deprecated (since := "2026-01-26")] alias all_ae_tendsto_ofReal_norm := ae_tendsto_ofReal_norm

Depends on / 依赖: ae_tendsto_enorm, convert
-/
theorem ae_tendsto_ofReal_norm (h : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop <| 𝓝 <| f a) :
forallᵐ a ∂μ, Tendsto (fun n => ENNReal.ofReal ‖F n a‖) atTop 𝓝 ENNReal.ofReal ‖f a‖ := by
  convert! ae_tendsto_enorm h <;> simp

@[deprecated (since := "2026-01-26")] alias all_ae_tendsto_ofReal_norm := ae_tendsto_ofReal_norm

/--
theorem `ae_norm_ofReal_f_le_bound` / 定理 `ae_norm_ofReal_f_le_bound`

English:
theorem ae_norm_ofReal_f_le_bound
  statement: (h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound a)
  proof: by
  have F_le_bound := all_ae_norm_ofReal_F_le_bound h_bound
  rw [← ae_all_iff] at F_le_bound
  apply F_le_bound.mp ((ae_tendsto_ofReal_norm h_lim).mono _)
  intro a tendsto_norm F_le_bound
  exact le_of_tendsto' tendsto_norm F_le_bound

@[deprecated (since := "2026-01-26")] alias all_ae_ofReal_f_

中文:
定理 ae_norm_of实数_f_le_bound
  结论: (h_bound : 对任意 n, 对任意ᵐ a ∂μ, ‖F n a‖ <= bound a)
  证明: by
  have F_le_bound := all_ae_norm_ofReal_F_le_bound h_bound
  rw [← ae_all_iff] at F_le_bound
  apply F_le_bound.mp ((ae_tendsto_ofReal_norm h_lim).mono _)
  intro a tendsto_norm F_le_bound
  exact le_of_tendsto' tendsto_norm F_le_bound

@[deprecated (since := "2026-01-26")] alias all_ae_ofReal_f_

Depends on / 依赖: F_le_bound, F_le_bound.mp, ae_all_iff, ae_tendsto_ofReal_norm, all_ae_norm_ofReal_F_le_bound, h_bound, h_lim, le_of_tendsto, tendsto_norm
-/
theorem ae_norm_ofReal_f_le_bound (h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound a)
    (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    forallᵐ a ∂μ, ENNReal.ofReal ‖f a‖ <= ENNReal.ofReal (bound a) := by
  have F_le_bound := all_ae_norm_ofReal_F_le_bound h_bound
  rw [← ae_all_iff] at F_le_bound
  apply F_le_bound.mp ((ae_tendsto_ofReal_norm h_lim).mono _)
  intro a tendsto_norm F_le_bound
  exact le_of_tendsto' tendsto_norm F_le_bound

@[deprecated (since := "2026-01-26")] alias all_ae_ofReal_f_le_bound := ae_norm_ofReal_f_le_bound

/--
theorem `ae_enorm_le_bound` / 定理 `ae_enorm_le_bound`

English:
theorem ae_enorm_le_bound
  statement: (h_bound : forall n, forallᵐ a ∂μ, ‖F' n a‖ₑ <= bound' a)
  proof: by
  rw [← ae_all_iff] at h_bound
  apply h_bound.mp ((ae_tendsto_enorm h_lim).mono _)
  intro a tendsto_norm h_bound
  exact le_of_tendsto' tendsto_norm h_bound

中文:
定理 ae_enorm_le_bound
  结论: (h_bound : 对任意 n, 对任意ᵐ a ∂μ, ‖F' n a‖ₑ <= bound' a)
  证明: by
  rw [← ae_all_iff] at h_bound
  apply h_bound.mp ((ae_tendsto_enorm h_lim).mono _)
  intro a tendsto_norm h_bound
  exact le_of_tendsto' tendsto_norm h_bound

Depends on / 依赖: ae_all_iff, ae_tendsto_enorm, h_bound, h_bound.mp, h_lim, le_of_tendsto, tendsto_norm
-/
theorem ae_enorm_le_bound (h_bound : forall n, forallᵐ a ∂μ, ‖F' n a‖ₑ <= bound' a)
    (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F' n a) atTop (𝓝 (f' a))) :
    forallᵐ a ∂μ, ‖f' a‖ₑ <= bound' a := by
  rw [← ae_all_iff] at h_bound
  apply h_bound.mp ((ae_tendsto_enorm h_lim).mono _)
  intro a tendsto_norm h_bound
  exact le_of_tendsto' tendsto_norm h_bound

/--
theorem `hasFiniteIntegral_of_dominated_convergence_enorm` / 定理 `hasFiniteIntegral_of_dominated_convergence_enorm`

English:
theorem hasFiniteIntegral_of_dominated_convergence_enorm
  proof: by
  /- `‖F' n a‖ₑ ≤ bound' a` and `‖F' n a‖ₑ --> ‖f' a‖ₑ` implies `‖f a‖ₑ ≤ bound' a`,
    and so `∫ ‖f'‖ₑ ≤ ∫ bound' < ∞` since `bound'` has finite integral -/
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ a, ‖f' a‖ₑ ∂μ) <= ∫⁻ a, bound' a ∂μ :=
lintegral_mono_ae ae_enorm_le_bound h_bound h_lim

中文:
定理 hasFinite整数egral_of_dominated_convergence_enorm
  证明: by
  /- `‖F' n a‖ₑ ≤ bound' a` and `‖F' n a‖ₑ --> ‖f' a‖ₑ` implies `‖f a‖ₑ ≤ bound' a`,
    and so `∫ ‖f'‖ₑ ≤ ∫ bound' < ∞` since `bound'` has finite integral -/
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ a, ‖f' a‖ₑ ∂μ) <= ∫⁻ a, bound' a ∂μ :=
lintegral_mono_ae ae_enorm_le_bound h_bound h_lim
-/
theorem hasFiniteIntegral_of_dominated_convergence_enorm
    (bound_hasFiniteIntegral : HasFiniteIntegral bound' μ)
    (h_bound : forall n, forallᵐ a ∂μ, ‖F' n a‖ₑ <= bound' a)
    (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F' n a) atTop (𝓝 (f' a))) : HasFiniteIntegral f' μ := by
  /- `‖F' n a‖ₑ ≤ bound' a` and `‖F' n a‖ₑ --> ‖f' a‖ₑ` implies `‖f a‖ₑ ≤ bound' a`,
    and so `∫ ‖f'‖ₑ ≤ ∫ bound' < ∞` since `bound'` has finite integral -/
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ a, ‖f' a‖ₑ ∂μ) <= ∫⁻ a, bound' a ∂μ :=
lintegral_mono_ae ae_enorm_le_bound h_bound h_lim
    _ < ∞ := bound_hasFiniteIntegral

/--
theorem `hasFiniteIntegral_of_dominated_convergence` / 定理 `hasFiniteIntegral_of_dominated_convergence`

English:
theorem hasFiniteIntegral_of_dominated_convergence
  proof: by
  /- `‖F n a‖ ≤ bound a` and `‖F n a‖ --> ‖f a‖` implies `‖f a‖ ≤ bound a`,
    and so `∫ ‖f‖ ≤ ∫ bound < ∞` since `bound` is has_finite_integral -/
  rw [hasFiniteIntegral_iff_norm]
  calc
    (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) <= ∫⁻ a, ENNReal.ofReal (bound a) ∂μ :=
lintegral_mono_ae ae_norm_ofRea

中文:
定理 hasFinite整数egral_of_dominated_convergence
  证明: by
  /- `‖F n a‖ ≤ bound a` and `‖F n a‖ --> ‖f a‖` implies `‖f a‖ ≤ bound a`,
    and so `∫ ‖f‖ ≤ ∫ bound < ∞` since `bound` is has_finite_integral -/
  rw [hasFiniteIntegral_iff_norm]
  calc
    (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) <= ∫⁻ a, ENNReal.ofReal (bound a) ∂μ :=
lintegral_mono_ae ae_norm_ofRea
-/
theorem hasFiniteIntegral_of_dominated_convergence
    (bound_hasFiniteIntegral : HasFiniteIntegral bound μ)
    (h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound a)
    (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) : HasFiniteIntegral f μ := by
  /- `‖F n a‖ ≤ bound a` and `‖F n a‖ --> ‖f a‖` implies `‖f a‖ ≤ bound a`,
    and so `∫ ‖f‖ ≤ ∫ bound < ∞` since `bound` is has_finite_integral -/
  rw [hasFiniteIntegral_iff_norm]
  calc
    (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ) <= ∫⁻ a, ENNReal.ofReal (bound a) ∂μ :=
lintegral_mono_ae ae_norm_ofReal_f_le_bound h_bound h_lim
    _ < ∞ := by
      rw [← hasFiniteIntegral_iff_ofReal]
      · exact bound_hasFiniteIntegral
      exact (h_bound 0).mono fun a h => le_trans (norm_nonneg _) h

-- TODO: generalise this to `f` and `F` taking values in a new class `ENormedSubmonoid`
/--
theorem `tendsto_lintegral_norm_of_dominated_convergence` / 定理 `tendsto_lintegral_norm_of_dominated_convergence`

English:
theorem tendsto_lintegral_norm_of_dominated_convergence
  proof: by
  have f_measurable : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ F_measurable h_lim
  let b a := 2 * ENNReal.ofReal (bound a)
  /- `‖F n a‖ ≤ bound a` and `F n a --> f a` implies `‖f a‖ ≤ bound a`, and thus by the
    triangle inequality, have `‖F n a - f a‖ ≤ 2 * (bound

中文:
定理 tendsto_lintegral_norm_of_dominated_convergence
  证明: by
  have f_measurable : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ F_measurable h_lim
  let b a := 2 * ENNReal.ofReal (bound a)
  /- `‖F n a‖ ≤ bound a` and `F n a --> f a` implies `‖f a‖ ≤ bound a`, and thus by the
    triangle inequality, have `‖F n a - f a‖ ≤ 2 * (bound

Depends on / 依赖: AEStronglyMeasurable, ENNReal, ENNReal.ofReal, F_measurable, aestronglyMeasurable_of_tendsto_ae, f_measurable, h_lim, ofReal
-/
theorem tendsto_lintegral_norm_of_dominated_convergence
    (F_measurable : forall n, AEStronglyMeasurable (F n) μ)
    (bound_hasFiniteIntegral : HasFiniteIntegral bound μ)
    (h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound a)
    (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, ENNReal.ofReal ‖F n a - f a‖ ∂μ) atTop (𝓝 0) := by
  have f_measurable : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae _ F_measurable h_lim
  let b a := 2 * ENNReal.ofReal (bound a)
  /- `‖F n a‖ ≤ bound a` and `F n a --> f a` implies `‖f a‖ ≤ bound a`, and thus by the
    triangle inequality, have `‖F n a - f a‖ ≤ 2 * (bound a)`. -/
  have hb : forall n, forallᵐ a ∂μ, ENNReal.ofReal ‖F n a - f a‖ <= b a := by
    intro n
    filter_upwards [all_ae_norm_ofReal_F_le_bound h_bound n,
      ae_norm_ofReal_f_le_bound h_bound h_lim] with a h₁ h₂
    calc
      ENNReal.ofReal ‖F n a - f a‖ <= ENNReal.ofReal ‖F n a‖ + ENNReal.ofReal ‖f a‖ := by
        rw [← ENNReal.ofReal_add]
        · apply ofReal_le_ofReal
          apply norm_sub_le
        · exact norm_nonneg _
        · exact norm_nonneg _
      _ <= ENNReal.ofReal (bound a) + ENNReal.ofReal (bound a) := add_le_add h₁ h₂
      _ = b a := by rw [← two_mul]
  -- On the other hand, `F n a --> f a` implies that `‖F n a - f a‖ --> 0`
  have h : forallᵐ a ∂μ, Tendsto (fun n => ENNReal.ofReal ‖F n a - f a‖) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    refine h_lim.mono fun a h => (continuous_ofReal.tendsto _).comp ?_
    rwa [← tendsto_iff_norm_sub_tendsto_zero]
  /- Therefore, by the dominated convergence theorem for nonnegative integration, have
    ` ∫ ‖f a - F n a‖ --> 0 ` -/
  suffices Tendsto (fun n => ∫⁻ a, ENNReal.ofReal ‖F n a - f a‖ ∂μ) atTop (𝓝 (∫⁻ _ : α, 0 ∂μ)) by
    rwa [lintegral_zero] at this
  -- Using the dominated convergence theorem.
  refine tendsto_lintegral_of_dominated_convergence' _ ?_ hb ?_ ?_
  -- Show `fun a => ‖f a - F n a‖` is almost everywhere measurable for all `n`
  · exact fun n =>
      measurable_ofReal.comp_aemeasurable ((F_measurable n).sub f_measurable).norm.aemeasurable
  -- Show `2 * bound` `HasFiniteIntegral`
  · rw [hasFiniteIntegral_iff_ofReal] at bound_hasFiniteIntegral
    · calc
        ∫⁻ a, b a ∂μ = 2 * ∫⁻ a, ENNReal.ofReal (bound a) ∂μ := by
          rw [lintegral_const_mul']
          finiteness
        _ != ∞ := mul_ne_top coe_ne_top bound_hasFiniteIntegral.ne
    filter_upwards [h_bound 0] with _ h using le_trans (norm_nonneg _) h
  -- Show `‖f a - F n a‖ --> 0`
  · exact h

end DominatedConvergence

section PosPart

/-! Lemmas used for defining the positive part of an `L¹` function -/

@[fun_prop]
/--
theorem `HasFiniteIntegral.max_zero` / 定理 `HasFiniteIntegral.max_zero`

English:
theorem HasFiniteIntegral.max_zero
  given: {f : α -> Real} (hf : HasFiniteIntegral f μ)
  proof: hf.mono Eventually.of_forall fun x => by simp [abs_le, le_abs_self]

@[fun_prop]

中文:
定理 HasFinite整数egral.max_zero
  条件: {f : α -> 实数} (hf : HasFinite整数egral f μ)
  证明: hf.mono Eventually.of_forall fun x => by simp [abs_le, le_abs_self]

@[fun_prop]

Depends on / 依赖: Eventually, Eventually.of_forall, abs_le, hf.mono, le_abs_self, of_forall
-/
theorem HasFiniteIntegral.max_zero {f : α -> Real} (hf : HasFiniteIntegral f μ) :
    HasFiniteIntegral (fun a => max (f a) 0) μ :=
hf.mono Eventually.of_forall fun x => by simp [abs_le, le_abs_self]

@[fun_prop]
/--
theorem `HasFiniteIntegral.min_zero` / 定理 `HasFiniteIntegral.min_zero`

English:
theorem HasFiniteIntegral.min_zero
  given: {f : α -> Real} (hf : HasFiniteIntegral f μ)
  proof: hf.mono Eventually.of_forall fun x => by simpa [abs_le] using neg_abs_le _

中文:
定理 HasFinite整数egral.min_zero
  条件: {f : α -> 实数} (hf : HasFinite整数egral f μ)
  证明: hf.mono Eventually.of_forall fun x => by simpa [abs_le] using neg_abs_le _

Depends on / 依赖: Eventually, Eventually.of_forall, abs_le, hf.mono, neg_abs_le, of_forall
-/
theorem HasFiniteIntegral.min_zero {f : α -> Real} (hf : HasFiniteIntegral f μ) :
    HasFiniteIntegral (fun a => min (f a) 0) μ :=
hf.mono Eventually.of_forall fun x => by simpa [abs_le] using neg_abs_le _

end PosPart

section NormedSpace

variable {𝕜 : Type*}

@[fun_prop]
/--
theorem `HasFiniteIntegral.smul` / 定理 `HasFiniteIntegral.smul`

English:
theorem HasFiniteIntegral.smul
  statement: [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 β] [IsBoundedSMul 𝕜 β]
  proof: by
  simp only [HasFiniteIntegral]
  calc
    ∫⁻ a : α, ‖c • f a‖ₑ ∂μ <= ∫⁻ a : α, ‖c‖ₑ * ‖f a‖ₑ ∂μ := lintegral_mono fun i => enorm_smul_le
    _ < ∞ := by
      rw [lintegral_const_mul']
      exacts [mul_lt_top coe_lt_top hf, coe_ne_top]

中文:
定理 HasFinite整数egral.smul
  结论: [赋范交换加群 𝕜] [SMulZero类 𝕜 β] [是BoundedSMul 𝕜 β]
  证明: by
  simp only [HasFiniteIntegral]
  calc
    ∫⁻ a : α, ‖c • f a‖ₑ ∂μ <= ∫⁻ a : α, ‖c‖ₑ * ‖f a‖ₑ ∂μ := lintegral_mono fun i => enorm_smul_le
    _ < ∞ := by
      rw [lintegral_const_mul']
      exacts [mul_lt_top coe_lt_top hf, coe_ne_top]

Depends on / 依赖: HasFiniteIntegral, coe_lt_top, coe_ne_top, enorm_smul_le, exacts, lintegral_const_mul, lintegral_mono, mul_lt_top
-/
theorem HasFiniteIntegral.smul [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 β] [IsBoundedSMul 𝕜 β]
    (c : 𝕜) {f : α -> β} (hf : HasFiniteIntegral f μ) :
    HasFiniteIntegral (c • f) μ := by
  simp only [HasFiniteIntegral]
  calc
    ∫⁻ a : α, ‖c • f a‖ₑ ∂μ <= ∫⁻ a : α, ‖c‖ₑ * ‖f a‖ₑ ∂μ := lintegral_mono fun i => enorm_smul_le
    _ < ∞ := by
      rw [lintegral_const_mul']
      exacts [mul_lt_top coe_lt_top hf, coe_ne_top]

-- TODO: weaken the hypothesis to a version of `ENormSMulClass` with `≤`,
-- once such a typeclass exists.
-- This will let us unify with `HasFiniteIntegral.smul` above.
@[fun_prop]
/--
theorem `HasFiniteIntegral.smul_enorm` / 定理 `HasFiniteIntegral.smul_enorm`

English:
theorem HasFiniteIntegral.smul_enorm
  statement: [NormedAddGroup 𝕜] [SMul 𝕜 ε''] [ENormSMulClass 𝕜 ε'']
  proof: by
  simp only [HasFiniteIntegral]
  calc
    ∫⁻ a : α, ‖c • f a‖ₑ ∂μ = ∫⁻ a : α, ‖c‖ₑ * ‖f a‖ₑ ∂μ := lintegral_congr fun i => enorm_smul _ _
    _ < ∞ := by
      rw [lintegral_const_mul']
      exacts [mul_lt_top coe_lt_top hf, coe_ne_top]

中文:
定理 HasFinite整数egral.smul_enorm
  结论: [赋范加群 𝕜] [标量乘法 𝕜 ε''] [ENormSMul类 𝕜 ε'']
  证明: by
  simp only [HasFiniteIntegral]
  calc
    ∫⁻ a : α, ‖c • f a‖ₑ ∂μ = ∫⁻ a : α, ‖c‖ₑ * ‖f a‖ₑ ∂μ := lintegral_congr fun i => enorm_smul _ _
    _ < ∞ := by
      rw [lintegral_const_mul']
      exacts [mul_lt_top coe_lt_top hf, coe_ne_top]

Depends on / 依赖: HasFiniteIntegral, coe_lt_top, coe_ne_top, enorm_smul, exacts, lintegral_congr, lintegral_const_mul, mul_lt_top
-/
theorem HasFiniteIntegral.smul_enorm [NormedAddGroup 𝕜] [SMul 𝕜 ε''] [ENormSMulClass 𝕜 ε'']
    (c : 𝕜) {f : α -> ε''} (hf : HasFiniteIntegral f μ) : HasFiniteIntegral (c • f) μ := by
  simp only [HasFiniteIntegral]
  calc
    ∫⁻ a : α, ‖c • f a‖ₑ ∂μ = ∫⁻ a : α, ‖c‖ₑ * ‖f a‖ₑ ∂μ := lintegral_congr fun i => enorm_smul _ _
    _ < ∞ := by
      rw [lintegral_const_mul']
      exacts [mul_lt_top coe_lt_top hf, coe_ne_top]

/--
theorem `hasFiniteIntegral_smul_iff` / 定理 `hasFiniteIntegral_smul_iff`

English:
theorem hasFiniteIntegral_smul_iff
  statement: [NormedRing 𝕜] [MulActionWithZero 𝕜 β] [IsBoundedSMul 𝕜 β]
  proof: by
  obtain ⟨c, rfl⟩ := hc
  constructor
  · intro h
    simpa only [smul_smul, Units.inv_mul, one_smul] using h.smul ((c⁻¹ : 𝕜ˣ) : 𝕜)
  exact HasFiniteIntegral.smul _

@[fun_prop]

中文:
定理 hasFinite整数egral_smul_iff
  结论: [赋范环 𝕜] [带零乘法作用 𝕜 β] [是BoundedSMul 𝕜 β]
  证明: by
  obtain ⟨c, rfl⟩ := hc
  constructor
  · intro h
    simpa only [smul_smul, Units.inv_mul, one_smul] using h.smul ((c⁻¹ : 𝕜ˣ) : 𝕜)
  exact HasFiniteIntegral.smul _

@[fun_prop]

Depends on / 依赖: HasFiniteIntegral, HasFiniteIntegral.smul, Units.inv_mul, h.smul, inv_mul, one_smul, smul_smul
-/
theorem hasFiniteIntegral_smul_iff [NormedRing 𝕜] [MulActionWithZero 𝕜 β] [IsBoundedSMul 𝕜 β]
    {c : 𝕜} (hc : IsUnit c) (f : α -> β) :
    HasFiniteIntegral (c • f) μ ↔ HasFiniteIntegral f μ := by
  obtain ⟨c, rfl⟩ := hc
  constructor
  · intro h
    simpa only [smul_smul, Units.inv_mul, one_smul] using h.smul ((c⁻¹ : 𝕜ˣ) : 𝕜)
  exact HasFiniteIntegral.smul _

@[fun_prop]
/--
theorem `HasFiniteIntegral.const_mul` / 定理 `HasFiniteIntegral.const_mul`

English:
theorem HasFiniteIntegral.const_mul
  given: [NormedRing 𝕜] {f : α -> 𝕜} (h : HasFiniteIntegral f μ) (c : 𝕜)
  proof: h.smul c

@[fun_prop]

中文:
定理 HasFinite整数egral.const_mul
  条件: [赋范环 𝕜] {f : α -> 𝕜} (h : HasFinite整数egral f μ) (c : 𝕜)
  证明: h.smul c

@[fun_prop]

Depends on / 依赖: h.smul
-/
theorem HasFiniteIntegral.const_mul [NormedRing 𝕜] {f : α -> 𝕜} (h : HasFiniteIntegral f μ) (c : 𝕜) :
    HasFiniteIntegral (fun x => c * f x) μ :=
  h.smul c

@[fun_prop]
/--
theorem `HasFiniteIntegral.mul_const` / 定理 `HasFiniteIntegral.mul_const`

English:
theorem HasFiniteIntegral.mul_const
  given: [NormedRing 𝕜] {f : α -> 𝕜} (h : HasFiniteIntegral f μ) (c : 𝕜)
  proof: h.smul (MulOpposite.op c)

中文:
定理 HasFinite整数egral.mul_const
  条件: [赋范环 𝕜] {f : α -> 𝕜} (h : HasFinite整数egral f μ) (c : 𝕜)
  证明: h.smul (MulOpposite.op c)

Depends on / 依赖: MulOpposite, MulOpposite.op, h.smul
-/
theorem HasFiniteIntegral.mul_const [NormedRing 𝕜] {f : α -> 𝕜} (h : HasFiniteIntegral f μ) (c : 𝕜) :
    HasFiniteIntegral (fun x => f x * c) μ :=
  h.smul (MulOpposite.op c)

section count

variable [MeasurableSingletonClass α]

-- Note that asking for mere summability makes no sense, as every sequence in ℝ≥0∞ is summable.
/--
lemma `hasFiniteIntegral_count_iff_enorm` / 引理 `hasFiniteIntegral_count_iff_enorm`

English:
lemma hasFiniteIntegral_count_iff_enorm
  given: {f : α -> ε}
  proof: by
  simp only [hasFiniteIntegral_iff_enorm, lintegral_count]

中文:
引理 hasFinite整数egral_count_iff_enorm
  条件: {f : α -> ε}
  证明: by
  simp only [hasFiniteIntegral_iff_enorm, lintegral_count]

Depends on / 依赖: hasFiniteIntegral_iff_enorm, lintegral_count
-/
lemma hasFiniteIntegral_count_iff_enorm {f : α -> ε} :
    HasFiniteIntegral f Measure.count ↔ tsum (‖f ·‖ₑ) < ⊤ := by
  simp only [hasFiniteIntegral_iff_enorm, lintegral_count]

/--
lemma `hasFiniteIntegral_count_iff` / 引理 `hasFiniteIntegral_count_iff`

English:
lemma hasFiniteIntegral_count_iff
  given: {f : α -> β}
  proof: by
  simp only [hasFiniteIntegral_iff_enorm, enorm, lintegral_count, lt_top_iff_ne_top,
    tsum_coe_ne_top_iff_summable, ← summable_coe, coe_nnnorm]

中文:
引理 hasFinite整数egral_count_iff
  条件: {f : α -> β}
  证明: by
  simp only [hasFiniteIntegral_iff_enorm, enorm, lintegral_count, lt_top_iff_ne_top,
    tsum_coe_ne_top_iff_summable, ← summable_coe, coe_nnnorm]

Depends on / 依赖: coe_nnnorm, hasFiniteIntegral_iff_enorm, lintegral_count, lt_top_iff_ne_top, summable_coe, tsum_coe_ne_top_iff_summable
-/
lemma hasFiniteIntegral_count_iff {f : α -> β} :
    HasFiniteIntegral f Measure.count ↔ Summable (‖f ·‖) := by
  simp only [hasFiniteIntegral_iff_enorm, enorm, lintegral_count, lt_top_iff_ne_top,
    tsum_coe_ne_top_iff_summable, ← summable_coe, coe_nnnorm]

end count

section restrict

variable {E : Type*} [NormedAddCommGroup E] {f : α -> ε}

@[fun_prop]
/--
lemma `HasFiniteIntegral.restrict` / 引理 `HasFiniteIntegral.restrict`

English:
lemma HasFiniteIntegral.restrict
  given: (h : HasFiniteIntegral f μ) {s : Set α}
  proof: by
  refine lt_of_le_of_lt ?_ h
  simpa [Measure.restrict_univ] using lintegral_mono_set (subset_univ s)

中文:
引理 HasFinite整数egral.restrict
  条件: (h : HasFinite整数egral f μ) {s : 集合 α}
  证明: by
  refine lt_of_le_of_lt ?_ h
  simpa [Measure.restrict_univ] using lintegral_mono_set (subset_univ s)

Depends on / 依赖: Measure, Measure.restrict_univ, lintegral_mono_set, lt_of_le_of_lt, restrict_univ, subset_univ
-/
lemma HasFiniteIntegral.restrict (h : HasFiniteIntegral f μ) {s : Set α} :
    HasFiniteIntegral f (μ.restrict s) := by
  refine lt_of_le_of_lt ?_ h
  simpa [Measure.restrict_univ] using lintegral_mono_set (subset_univ s)

end restrict

end NormedSpace

end MeasureTheory
