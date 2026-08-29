/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Etienne Marion
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Bochner integral of a function against the composition and the composition-products of two kernels

We prove properties of the composition and the composition-product of two kernels.

If `κ` is a kernel from `α` to `β` and `η` is a kernel from `β` to `γ`, we can form their
composition `η ∘ₖ κ : Kernel α γ`. We proved in `ProbabilityTheory.Kernel.lintegral_comp` that it
verifies `∫⁻ c, f c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, f c ∂(η b) ∂(κ a)`. In this file, we
prove the same equality for the Bochner integral.

If `κ` is an s-finite kernel from `α` to `β` and `η` is an s-finite kernel from `α × β` to `γ`,
we can form their composition-product `κ ⊗ₖ η : Kernel α (β × γ)`.
We proved in `ProbabilityTheory.Kernel.lintegral_compProd` that it
verifies `∫⁻ bc, f bc ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`. In this file, we
prove the same equality for the Bochner integral.

## Main statements

* `ProbabilityTheory.integral_compProd`: the integral against the composition-product is
  `∫ z, f z ∂((κ ⊗ₖ η) a) = ∫ x, ∫ y, f (x, y) ∂(η (a, x)) ∂(κ a)`.

* `ProbabilityTheory.integral_comp`: the integral against the composition is
  `∫⁻ z, f z ∂((η ∘ₖ κ) a) = ∫⁻ x, ∫⁻ y, f y ∂(η x) ∂(κ a)`.

## Implementation details

This file is to a large extent a copy of part of `Mathlib/MeasureTheory/Integral/Prod.lean`.
The product of two measures is a particular case of composition-product of kernels and
it turns out that once the measurability of the Lebesgue integral of a kernel is proved,
almost all proofs about integrals against products of measures extend with minimal modifications
to the composition-product of two kernels.

The composition of kernels can also be expressed easily with the composition-product and therefore
the proofs about the composition are only simplified versions of the ones for the
composition-product. However it is necessary to do all the proofs once again because the
composition-product requires s-finiteness while the composition does not.
-/

public section


noncomputable section

open Set Function Real ENNReal MeasureTheory Filter ProbabilityTheory ProbabilityTheory.Kernel
open scoped Topology ENNReal MeasureTheory

variable {α β γ E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} [NormedAddCommGroup E] {a : α}

namespace ProbabilityTheory

section compProd

variable {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel (α × β) γ} [IsSFiniteKernel η]

/--
theorem `hasFiniteIntegral_prodMk_left` / 定理 `hasFiniteIntegral_prodMk_left`

English:
theorem hasFiniteIntegral_prodMk_left
  given: (a : α) {s : Set (β × γ)} (h2s : (κ otimesₖ η) a s != ∞)
  proof: by
  let t := toMeasurable ((κ otimesₖ η) a) s
  simp_rw [hasFiniteIntegral_iff_enorm, measureReal_def, enorm_eq_ofReal toReal_nonneg]
  calc
    ∫⁻ b, ENNReal.ofReal (η (a, b) (Prod.mk b ⁻¹' s)).toReal ∂κ a
    _ <= ∫⁻ b, η (a, b) (Prod.mk b ⁻¹' t) ∂κ a := by
      refine lintegral_mono_ae ?_
     

中文:
定理 hasFiniteIntegral_prodMk_left
  条件: (a : α) {s : Set (β × γ)} (h2s : (κ otimesₖ η) a s != ∞)
  证明: by
  let t := toMeasurable ((κ otimesₖ η) a) s
  simp_rw [hasFiniteIntegral_iff_enorm, measureReal_def, enorm_eq_ofReal toReal_nonneg]
  calc
    ∫⁻ b, ENNReal.ofReal (η (a, b) (Prod.mk b ⁻¹' s)).toReal ∂κ a
    _ <= ∫⁻ b, η (a, b) (Prod.mk b ⁻¹' t) ∂κ a := by
      refine lintegral_mono_ae ?_
     

Depends on / 依赖: ENNReal, ENNReal.ofReal, Prod.mk, ae_kernel_lt_top, enorm_eq_ofReal, filter_upwards, hasFiniteIntegral_iff_enorm, hb.ne, le_compProd_apply, lintegral_mono_ae, measureReal_def, measure_mono, measure_toMe, ofReal, ofReal_toReal, preimage_mono, simp_rw, subset_toMeasurable, toMeasurable, toReal
-/
theorem hasFiniteIntegral_prodMk_left (a : α) {s : Set (β × γ)} (h2s : (κ otimesₖ η) a s != ∞) :
    HasFiniteIntegral (fun b => (η (a, b)).real (Prod.mk b ⁻¹' s)) (κ a) := by
  let t := toMeasurable ((κ otimesₖ η) a) s
  simp_rw [hasFiniteIntegral_iff_enorm, measureReal_def, enorm_eq_ofReal toReal_nonneg]
  calc
    ∫⁻ b, ENNReal.ofReal (η (a, b) (Prod.mk b ⁻¹' s)).toReal ∂κ a
    _ <= ∫⁻ b, η (a, b) (Prod.mk b ⁻¹' t) ∂κ a := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_kernel_lt_top a h2s] with b hb
      rw [ofReal_toReal hb.ne]
      exact measure_mono (preimage_mono (subset_toMeasurable _ _))
    _ <= (κ otimesₖ η) a t := le_compProd_apply _ _ _ _
    _ = (κ otimesₖ η) a s := measure_toMeasurable s
    _ < ⊤ := h2s.lt_top

/--
theorem `integrable_kernel_prodMk_left` / 定理 `integrable_kernel_prodMk_left`

English:
theorem integrable_kernel_prodMk_left
  statement: (a : α) {s : Set (β × γ)} (hs : MeasurableSet s)
  proof: by
  constructor
  · exact (measurable_kernel_prodMk_left' hs a).ennreal_toReal.aestronglyMeasurable
  · exact hasFiniteIntegral_prodMk_left a h2s

中文:
定理 integrable_kernel_prodMk_left
  结论: (a : α) {s : Set (β × γ)} (hs : MeasurableSet s)
  证明: by
  constructor
  · exact (measurable_kernel_prodMk_left' hs a).ennreal_toReal.aestronglyMeasurable
  · exact hasFiniteIntegral_prodMk_left a h2s

Depends on / 依赖: aestronglyMeasurable, ennreal_toReal, ennreal_toReal.aestronglyMeasurable, hasFiniteIntegral_prodMk_left, measurable_kernel_prodMk_left
-/
theorem integrable_kernel_prodMk_left (a : α) {s : Set (β × γ)} (hs : MeasurableSet s)
    (h2s : (κ otimesₖ η) a s != ∞) : Integrable (fun b => (η (a, b)).real (Prod.mk b ⁻¹' s)) (κ a) := by
  constructor
  · exact (measurable_kernel_prodMk_left' hs a).ennreal_toReal.aestronglyMeasurable
  · exact hasFiniteIntegral_prodMk_left a h2s

/--
theorem `_root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_compProd` / 定理 `_root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_compProd`

English:
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_compProd
  statement: [NormedSpace Real E]
  proof: ⟨fun x => ∫ y, hf.mk f (x, y) ∂η (a, x), hf.stronglyMeasurable_mk.integral_kernel_prod_right'', by
    filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩

中文:
定理 _root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_compProd
  结论: [NormedSpace 实数 E]
  证明: ⟨fun x => ∫ y, hf.mk f (x, y) ∂η (a, x), hf.stronglyMeasurable_mk.integral_kernel_prod_right'', by
    filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩

Depends on / 依赖: ae_ae_of_ae_compProd, ae_eq_mk, filter_upwards, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk.integral_kernel_prod_right, integral_congr_ae, integral_kernel_prod_right, stronglyMeasurable_mk
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_compProd [NormedSpace Real E]
    ⦃f : β × γ -> E⦄ (hf : AEStronglyMeasurable f ((κ otimesₖ η) a)) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂η (a, x)) (κ a) :=
  ⟨fun x => ∫ y, hf.mk f (x, y) ∂η (a, x), hf.stronglyMeasurable_mk.integral_kernel_prod_right'', by
    filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩

/--
theorem `_root_.MeasureTheory.AEStronglyMeasurable.compProd_mk_left` / 定理 `_root_.MeasureTheory.AEStronglyMeasurable.compProd_mk_left`

English:
theorem _root_.MeasureTheory.AEStronglyMeasurable.compProd_mk_left
  statement: {δ : Type*} [TopologicalSpace δ]
  proof: by
  filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with x hx using
    ⟨fun y => hf.mk f (x, y), hf.stronglyMeasurable_mk.comp_measurable measurable_prodMk_left, hx⟩

中文:
定理 _root_.MeasureTheory.AEStronglyMeasurable.compProd_mk_left
  结论: {δ : 类型} [TopologicalSpace δ]
  证明: by
  filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with x hx using
    ⟨fun y => hf.mk f (x, y), hf.stronglyMeasurable_mk.comp_measurable measurable_prodMk_left, hx⟩

Depends on / 依赖: ae_ae_of_ae_compProd, ae_eq_mk, comp_measurable, filter_upwards, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk.comp_measurable, measurable_prodMk_left, stronglyMeasurable_mk
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.compProd_mk_left {δ : Type*} [TopologicalSpace δ]
    {f : β × γ -> δ} (hf : AEStronglyMeasurable f ((κ otimesₖ η) a)) :
    forallᵐ x ∂κ a, AEStronglyMeasurable (fun y => f (x, y)) (η (a, x)) := by
  filter_upwards [ae_ae_of_ae_compProd hf.ae_eq_mk] with x hx using
    ⟨fun y => hf.mk f (x, y), hf.stronglyMeasurable_mk.comp_measurable measurable_prodMk_left, hx⟩



/--
theorem `hasFiniteIntegral_compProd_iff` / 定理 `hasFiniteIntegral_compProd_iff`

English:
theorem hasFiniteIntegral_compProd_iff
  given: ⦃f
  statement: β × γ -> E⦄ (h1f : StronglyMeasurable f) :
  proof: by
  simp only [hasFiniteIntegral_iff_enorm]
  rw [lintegral_compProd _ _ _ h1f.enorm]
  have : forall x, forallᵐ y ∂η (a, x), 0 <= ‖f (x, y)‖ := fun x => Eventually.of_forall fun y => norm_nonneg _
  simp_rw [integral_eq_lintegral_of_nonneg_ae (this _)
      (h1f.norm.comp_measurable measurable_pro

中文:
定理 hasFiniteIntegral_compProd_iff
  条件: ⦃f
  结论: β × γ -> E⦄ (h1f : StronglyMeasurable f) :
  证明: by
  simp only [hasFiniteIntegral_iff_enorm]
  rw [lintegral_compProd _ _ _ h1f.enorm]
  have : forall x, forallᵐ y ∂η (a, x), 0 <= ‖f (x, y)‖ := fun x => Eventually.of_forall fun y => norm_nonneg _
  simp_rw [integral_eq_lintegral_of_nonneg_ae (this _)
      (h1f.norm.comp_measurable measurable_pro

Depends on / 依赖: Eventually, Eventually.of_forall, aestronglyMeasurable, and_congr_right_iff, and_iff_righ, comp_measurable, enorm_eq_ofReal, h1f.enorm, h1f.norm.comp_measurable, hasFiniteIntegral_iff_enorm, integral_eq_lintegral_of_nonneg_ae, lintegral_compProd, measurable_prodMk_left, norm_nonneg, ofReal_norm, of_forall, simp_rw, toReal_nonneg
-/
theorem hasFiniteIntegral_compProd_iff ⦃f : β × γ -> E⦄ (h1f : StronglyMeasurable f) :
    HasFiniteIntegral f ((κ otimesₖ η) a) ↔
      (forallᵐ x ∂κ a, HasFiniteIntegral (fun y => f (x, y)) (η (a, x))) ∧
        HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂η (a, x)) (κ a) := by
  simp only [hasFiniteIntegral_iff_enorm]
  rw [lintegral_compProd _ _ _ h1f.enorm]
  have : forall x, forallᵐ y ∂η (a, x), 0 <= ‖f (x, y)‖ := fun x => Eventually.of_forall fun y => norm_nonneg _
  simp_rw [integral_eq_lintegral_of_nonneg_ae (this _)
      (h1f.norm.comp_measurable measurable_prodMk_left).aestronglyMeasurable,
    enorm_eq_ofReal toReal_nonneg, ofReal_norm]
  have : forall {p q r : Prop} (_ : r -> p), (r ↔ p ∧ q) ↔ p -> (r ↔ q) := fun {p q r} h1 => by
    rw [← and_congr_right_iff]; rw [and_iff_right_of_imp h1]
  rw [this]
  · intro h2f; rw [lintegral_congr_ae]
    filter_upwards [h2f] with x hx
    rw [ofReal_toReal]; finiteness
  · intro h2f; refine ae_lt_top ?_ h2f.ne; exact h1f.enorm.lintegral_kernel_prod_right''

/--
theorem `hasFiniteIntegral_compProd_iff'` / 定理 `hasFiniteIntegral_compProd_iff'`

English:
theorem hasFiniteIntegral_compProd_iff'
  given: ⦃f
  statement: β × γ -> E⦄
  proof: by
  rw [hasFiniteIntegral_congr h1f.ae_eq_mk]; rw [hasFiniteIntegral_compProd_iff h1f.stronglyMeasurable_mk]
  apply and_congr
  · apply eventually_congr
    filter_upwards [ae_ae_of_ae_compProd h1f.ae_eq_mk.symm] with x hx using
      hasFiniteIntegral_congr hx
  · apply hasFiniteIntegral_congr
  

中文:
定理 hasFiniteIntegral_compProd_iff'
  条件: ⦃f
  结论: β × γ -> E⦄
  证明: by
  rw [hasFiniteIntegral_congr h1f.ae_eq_mk]; rw [hasFiniteIntegral_compProd_iff h1f.stronglyMeasurable_mk]
  apply and_congr
  · apply eventually_congr
    filter_upwards [ae_ae_of_ae_compProd h1f.ae_eq_mk.symm] with x hx using
      hasFiniteIntegral_congr hx
  · apply hasFiniteIntegral_congr
  

Depends on / 依赖: EventuallyEq, EventuallyEq.fun_comp, ae_ae_of_ae_compProd, ae_eq_mk, and_congr, eventually_congr, filter_upwards, fun_comp, h1f.ae_eq_mk, h1f.ae_eq_mk.symm, h1f.stronglyMeasurable_mk, hasFiniteIntegral_compProd_iff, hasFiniteIntegral_congr, integral_congr_ae, stronglyMeasurable_mk
-/
theorem hasFiniteIntegral_compProd_iff' ⦃f : β × γ -> E⦄
    (h1f : AEStronglyMeasurable f ((κ otimesₖ η) a)) :
    HasFiniteIntegral f ((κ otimesₖ η) a) ↔
      (forallᵐ x ∂κ a, HasFiniteIntegral (fun y => f (x, y)) (η (a, x))) ∧
        HasFiniteIntegral (fun x => ∫ y, ‖f (x, y)‖ ∂η (a, x)) (κ a) := by
  rw [hasFiniteIntegral_congr h1f.ae_eq_mk]; rw [hasFiniteIntegral_compProd_iff h1f.stronglyMeasurable_mk]
  apply and_congr
  · apply eventually_congr
    filter_upwards [ae_ae_of_ae_compProd h1f.ae_eq_mk.symm] with x hx using
      hasFiniteIntegral_congr hx
  · apply hasFiniteIntegral_congr
    filter_upwards [ae_ae_of_ae_compProd h1f.ae_eq_mk.symm] with _ hx using
      integral_congr_ae (EventuallyEq.fun_comp hx _)

/--
theorem `integrable_compProd_iff` / 定理 `integrable_compProd_iff`

English:
theorem integrable_compProd_iff
  given: ⦃f
  statement: β × γ -> E⦄ (hf : AEStronglyMeasurable f ((κ otimesₖ η) a)) :
  proof: by
  simp only [Integrable, hasFiniteIntegral_compProd_iff' hf, hf.norm.integral_kernel_compProd,
    hf, hf.compProd_mk_left, eventually_and, true_and]

中文:
定理 integrable_compProd_iff
  条件: ⦃f
  结论: β × γ -> E⦄ (hf : AEStronglyMeasurable f ((κ otimesₖ η) a)) :
  证明: by
  simp only [Integrable, hasFiniteIntegral_compProd_iff' hf, hf.norm.integral_kernel_compProd,
    hf, hf.compProd_mk_left, eventually_and, true_and]

Depends on / 依赖: Integrable, compProd_mk_left, eventually_and, ha.mono, hasEval_iff, hasFiniteIntegral_compProd_iff, hf.compProd_mk_left, hf.norm.integral_kernel_compProd, integral_kernel_compProd, true_and
-/
theorem integrable_compProd_iff ⦃f : β × γ -> E⦄ (hf : AEStronglyMeasurable f ((κ otimesₖ η) a)) :
    Integrable f ((κ otimesₖ η) a) ↔
      (forallᵐ x ∂κ a, Integrable (fun y => f (x, y)) (η (a, x))) ∧
        Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂η (a, x)) (κ a) := by
  simp only [Integrable, hasFiniteIntegral_compProd_iff' hf, hf.norm.integral_kernel_compProd,
    hf, hf.compProd_mk_left, eventually_and, true_and]

/--
theorem `_root_.MeasureTheory.Integrable.ae_of_compProd` / 定理 `_root_.MeasureTheory.Integrable.ae_of_compProd`

English:
theorem _root_.MeasureTheory.Integrable.ae_of_compProd
  given: ⦃f
  statement: β × γ -> E⦄
  proof: ((integrable_compProd_iff hf.aestronglyMeasurable).mp hf).1

中文:
定理 _root_.MeasureTheory.Integrable.ae_of_compProd
  条件: ⦃f
  结论: β × γ -> E⦄
  证明: ((integrable_compProd_iff hf.aestronglyMeasurable).mp hf).1

Depends on / 依赖: HasEval, MvPowerSeries, MvPowerSeries.HasEval.zero, aestronglyMeasurable, hasEval_iff, hf.aestronglyMeasurable, integrable_compProd_iff
-/
theorem _root_.MeasureTheory.Integrable.ae_of_compProd ⦃f : β × γ -> E⦄
    (hf : Integrable f ((κ otimesₖ η) a)) : forallᵐ x ∂κ a, Integrable (fun y => f (x, y)) (η (a, x)) :=
  ((integrable_compProd_iff hf.aestronglyMeasurable).mp hf).1

/--
theorem `_root_.MeasureTheory.Integrable.integral_norm_compProd` / 定理 `_root_.MeasureTheory.Integrable.integral_norm_compProd`

English:
theorem _root_.MeasureTheory.Integrable.integral_norm_compProd
  given: ⦃f
  statement: β × γ -> E⦄
  proof: ((integrable_compProd_iff hf.aestronglyMeasurable).mp hf).2

中文:
定理 _root_.MeasureTheory.Integrable.integral_norm_compProd
  条件: ⦃f
  结论: β × γ -> E⦄
  证明: ((integrable_compProd_iff hf.aestronglyMeasurable).mp hf).2

Depends on / 依赖: aestronglyMeasurable, ha.add, hasEval_iff, hf.aestronglyMeasurable, integrable_compProd_iff
-/
theorem _root_.MeasureTheory.Integrable.integral_norm_compProd ⦃f : β × γ -> E⦄
    (hf : Integrable f ((κ otimesₖ η) a)) : Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂η (a, x)) (κ a) :=
  ((integrable_compProd_iff hf.aestronglyMeasurable).mp hf).2

/--
theorem `_root_.MeasureTheory.Integrable.integral_compProd` / 定理 `_root_.MeasureTheory.Integrable.integral_compProd`

English:
theorem _root_.MeasureTheory.Integrable.integral_compProd
  statement: [NormedSpace Real E]
  proof: Integrable.mono hf.integral_norm_compProd hf.aestronglyMeasurable.integral_kernel_compProd
    Eventually.of_forall fun x =>
(norm_integral_le_integral_norm _).trans_eq
        (norm_of_nonneg <|
integral_nonneg_of_ae
              Eventually.of_forall fun y => (norm_nonneg (f (x, y)) :)).symm

中文:
定理 _root_.MeasureTheory.Integrable.integral_compProd
  结论: [NormedSpace 实数 E]
  证明: Integrable.mono hf.integral_norm_compProd hf.aestronglyMeasurable.integral_kernel_compProd
    Eventually.of_forall fun x =>
(norm_integral_le_integral_norm _).trans_eq
        (norm_of_nonneg <|
integral_nonneg_of_ae
              Eventually.of_forall fun y => (norm_nonneg (f (x, y)) :)).symm

Depends on / 依赖: Eventually, Eventually.of_forall, Integrable, Integrable.mono, aestronglyMeasurable, hasEval_iff, hf.aestronglyMeasurable.integral_kernel_compProd, hf.integral_norm_compProd, hx.mul_left, integral_kernel_compProd, integral_nonneg_of_ae, integral_norm_compProd, mul_left, norm_integral_le_integral_norm, norm_nonneg, norm_of_nonneg, of_forall, trans_eq
-/
theorem _root_.MeasureTheory.Integrable.integral_compProd [NormedSpace Real E]
    ⦃f : β × γ -> E⦄ (hf : Integrable f ((κ otimesₖ η) a)) :
    Integrable (fun x => ∫ y, f (x, y) ∂η (a, x)) (κ a) :=
Integrable.mono hf.integral_norm_compProd hf.aestronglyMeasurable.integral_kernel_compProd
    Eventually.of_forall fun x =>
(norm_integral_le_integral_norm _).trans_eq
        (norm_of_nonneg <|
integral_nonneg_of_ae
              Eventually.of_forall fun y => (norm_nonneg (f (x, y)) :)).symm

/-! ### Bochner integral -/


variable [NormedSpace Real E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace Real E']

/--
theorem `Kernel.integral_fn_integral_add` / 定理 `Kernel.integral_fn_integral_add`

English:
theorem Kernel.integral_fn_integral_add
  given: ⦃f g
  statement: β × γ -> E⦄ (F : E -> E')
  proof: by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_compProd, hg.ae_of_compProd] with _ h2f h2g
  simp [integral_add h2f h2g]

中文:
定理 Kernel.integral_fn_integral_add
  条件: ⦃f g
  结论: β × γ -> E⦄ (F : E -> E')
  证明: by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_compProd, hg.ae_of_compProd] with _ h2f h2g
  simp [integral_add h2f h2g]

Depends on / 依赖: ae_of_compProd, filter_upwards, hasEval_iff, hf.ae_of_compProd, hg.ae_of_compProd, hx.mul_right, integral_add, integral_congr_ae, mul_right
-/
theorem Kernel.integral_fn_integral_add ⦃f g : β × γ -> E⦄ (F : E -> E')
    (hf : Integrable f ((κ otimesₖ η) a)) (hg : Integrable g ((κ otimesₖ η) a)) :
    ∫ x, F (∫ y, f (x, y) + g (x, y) ∂η (a, x)) ∂κ a =
      ∫ x, F (∫ y, f (x, y) ∂η (a, x) + ∫ y, g (x, y) ∂η (a, x)) ∂κ a := by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_compProd, hg.ae_of_compProd] with _ h2f h2g
  simp [integral_add h2f h2g]

/--
theorem `Kernel.integral_fn_integral_sub` / 定理 `Kernel.integral_fn_integral_sub`

English:
theorem Kernel.integral_fn_integral_sub
  given: ⦃f g
  statement: β × γ -> E⦄ (F : E -> E')
  proof: by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_compProd, hg.ae_of_compProd] with _ h2f h2g
  simp [integral_sub h2f h2g]

中文:
定理 Kernel.integral_fn_integral_sub
  条件: ⦃f g
  结论: β × γ -> E⦄ (F : E -> E')
  证明: by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_compProd, hg.ae_of_compProd] with _ h2f h2g
  simp [integral_sub h2f h2g]

Depends on / 依赖: ae_of_compProd, filter_upwards, ha.map, hasEval_iff, hf.ae_of_compProd, hg.ae_of_compProd, integral_congr_ae, integral_sub
-/
theorem Kernel.integral_fn_integral_sub ⦃f g : β × γ -> E⦄ (F : E -> E')
    (hf : Integrable f ((κ otimesₖ η) a)) (hg : Integrable g ((κ otimesₖ η) a)) :
    ∫ x, F (∫ y, f (x, y) - g (x, y) ∂η (a, x)) ∂κ a =
      ∫ x, F (∫ y, f (x, y) ∂η (a, x) - ∫ y, g (x, y) ∂η (a, x)) ∂κ a := by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_compProd, hg.ae_of_compProd] with _ h2f h2g
  simp [integral_sub h2f h2g]

/--
theorem `Kernel.lintegral_fn_integral_sub` / 定理 `Kernel.lintegral_fn_integral_sub`

English:
theorem Kernel.lintegral_fn_integral_sub
  given: ⦃f g
  statement: β × γ -> E⦄ (F : E -> Real>=0∞)
  proof: by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.ae_of_compProd, hg.ae_of_compProd] with _ h2f h2g
  simp [integral_sub h2f h2g]

中文:
定理 Kernel.lintegral_fn_integral_sub
  条件: ⦃f g
  结论: β × γ -> E⦄ (F : E -> 实数>=0∞)
  证明: by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.ae_of_compProd, hg.ae_of_compProd] with _ h2f h2g
  simp [integral_sub h2f h2g]

Depends on / 依赖: ae_of_compProd, filter_upwards, hf.ae_of_compProd, hg.ae_of_compProd, integral_sub, lintegral_congr_ae
-/
theorem Kernel.lintegral_fn_integral_sub ⦃f g : β × γ -> E⦄ (F : E -> Real>=0∞)
    (hf : Integrable f ((κ otimesₖ η) a)) (hg : Integrable g ((κ otimesₖ η) a)) :
    ∫⁻ x, F (∫ y, f (x, y) - g (x, y) ∂η (a, x)) ∂κ a =
      ∫⁻ x, F (∫ y, f (x, y) ∂η (a, x) - ∫ y, g (x, y) ∂η (a, x)) ∂κ a := by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.ae_of_compProd, hg.ae_of_compProd] with _ h2f h2g
  simp [integral_sub h2f h2g]

/--
theorem `Kernel.integral_integral_add` / 定理 `Kernel.integral_integral_add`

English:
theorem Kernel.integral_integral_add
  given: ⦃f g
  statement: β × γ -> E⦄ (hf : Integrable f ((κ otimesₖ η) a))
  proof: (Kernel.integral_fn_integral_add id hf hg).trans
    integral_add hf.integral_compProd hg.integral_compProd

中文:
定理 Kernel.integral_integral_add
  条件: ⦃f g
  结论: β × γ -> E⦄ (hf : 整数egrable f ((κ otimesₖ η) a))
  证明: (Kernel.integral_fn_integral_add id hf hg).trans
    integral_add hf.integral_compProd hg.integral_compProd

Depends on / 依赖: Kernel, Kernel.integral_fn_integral_add, hf.integral_compProd, hg.integral_compProd, integral_add, integral_compProd, integral_fn_integral_add
-/
theorem Kernel.integral_integral_add ⦃f g : β × γ -> E⦄ (hf : Integrable f ((κ otimesₖ η) a))
    (hg : Integrable g ((κ otimesₖ η) a)) :
    ∫ x, ∫ y, f (x, y) + g (x, y) ∂η (a, x) ∂κ a =
      ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a + ∫ x, ∫ y, g (x, y) ∂η (a, x) ∂κ a :=
(Kernel.integral_fn_integral_add id hf hg).trans
    integral_add hf.integral_compProd hg.integral_compProd

/--
theorem `Kernel.integral_integral_add'` / 定理 `Kernel.integral_integral_add'`

English:
theorem Kernel.integral_integral_add'
  given: ⦃f g
  statement: β × γ -> E⦄ (hf : Integrable f ((κ otimesₖ η) a))
  proof: Kernel.integral_integral_add hf hg

中文:
定理 Kernel.integral_integral_add'
  条件: ⦃f g
  结论: β × γ -> E⦄ (hf : 整数egrable f ((κ otimesₖ η) a))
  证明: Kernel.integral_integral_add hf hg

Depends on / 依赖: Kernel, Kernel.integral_integral_add, integral_integral_add
-/
theorem Kernel.integral_integral_add' ⦃f g : β × γ -> E⦄ (hf : Integrable f ((κ otimesₖ η) a))
    (hg : Integrable g ((κ otimesₖ η) a)) :
    ∫ x, ∫ y, (f + g) (x, y) ∂η (a, x) ∂κ a =
      ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a + ∫ x, ∫ y, g (x, y) ∂η (a, x) ∂κ a :=
  Kernel.integral_integral_add hf hg

/--
theorem `Kernel.integral_integral_sub` / 定理 `Kernel.integral_integral_sub`

English:
theorem Kernel.integral_integral_sub
  given: ⦃f g
  statement: β × γ -> E⦄ (hf : Integrable f ((κ otimesₖ η) a))
  proof: (Kernel.integral_fn_integral_sub id hf hg).trans
    integral_sub hf.integral_compProd hg.integral_compProd

中文:
定理 Kernel.integral_integral_sub
  条件: ⦃f g
  结论: β × γ -> E⦄ (hf : 整数egrable f ((κ otimesₖ η) a))
  证明: (Kernel.integral_fn_integral_sub id hf hg).trans
    integral_sub hf.integral_compProd hg.integral_compProd

Depends on / 依赖: Kernel, Kernel.integral_fn_integral_sub, hf.integral_compProd, hg.integral_compProd, integral_compProd, integral_fn_integral_sub, integral_sub
-/
theorem Kernel.integral_integral_sub ⦃f g : β × γ -> E⦄ (hf : Integrable f ((κ otimesₖ η) a))
    (hg : Integrable g ((κ otimesₖ η) a)) :
    ∫ x, ∫ y, f (x, y) - g (x, y) ∂η (a, x) ∂κ a =
      ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a - ∫ x, ∫ y, g (x, y) ∂η (a, x) ∂κ a :=
(Kernel.integral_fn_integral_sub id hf hg).trans
    integral_sub hf.integral_compProd hg.integral_compProd

/--
theorem `Kernel.integral_integral_sub'` / 定理 `Kernel.integral_integral_sub'`

English:
theorem Kernel.integral_integral_sub'
  given: ⦃f g
  statement: β × γ -> E⦄ (hf : Integrable f ((κ otimesₖ η) a))
  proof: Kernel.integral_integral_sub hf hg

中文:
定理 Kernel.integral_integral_sub'
  条件: ⦃f g
  结论: β × γ -> E⦄ (hf : 整数egrable f ((κ otimesₖ η) a))
  证明: Kernel.integral_integral_sub hf hg

Depends on / 依赖: Kernel, Kernel.integral_integral_sub, integral_integral_sub
-/
theorem Kernel.integral_integral_sub' ⦃f g : β × γ -> E⦄ (hf : Integrable f ((κ otimesₖ η) a))
    (hg : Integrable g ((κ otimesₖ η) a)) :
    ∫ x, ∫ y, (f - g) (x, y) ∂η (a, x) ∂κ a =
      ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a - ∫ x, ∫ y, g (x, y) ∂η (a, x) ∂κ a :=
  Kernel.integral_integral_sub hf hg

/--
theorem `Kernel.continuous_integral_integral` / 定理 `Kernel.continuous_integral_integral`

English:
theorem Kernel.continuous_integral_integral
  proof: by
  rw [continuous_iff_continuousAt]; intro g
  refine
    tendsto_integral_of_L1 _ (L1.integrable_coeFn g).integral_compProd.aestronglyMeasurable
      (Eventually.of_forall fun h => (L1.integrable_coeFn h).integral_compProd) ?_
  simp_rw [← lintegral_fn_integral_sub (‖·‖ₑ) (L1.integrable_coeFn _)

中文:
定理 Kernel.continuous_integral_integral
  证明: by
  rw [continuous_iff_continuousAt]; intro g
  refine
    tendsto_integral_of_L1 _ (L1.integrable_coeFn g).integral_compProd.aestronglyMeasurable
      (Eventually.of_forall fun h => (L1.integrable_coeFn h).integral_compProd) ?_
  simp_rw [← lintegral_fn_integral_sub (‖·‖ₑ) (L1.integrable_coeFn _)

Depends on / 依赖: Eventually, Eventually.of_forall, L1.integrable_coeFn, aestronglyMeasurable, continuous_iff_continuousAt, integrable_coeFn, integral_compProd, integral_compProd.aestronglyMeasurable, lintegral_, lintegral_fn_integral_sub, of_forall, simp_rw, tendsto_const_nhds, tendsto_integral_of_L1, tendsto_of_tendsto_of_tendsto_of_le_of_le, zero_le
-/
theorem Kernel.continuous_integral_integral :
    Continuous fun f : β × γ ->₁[(κ otimesₖ η) a] E => ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a := by
  rw [continuous_iff_continuousAt]; intro g
  refine
    tendsto_integral_of_L1 _ (L1.integrable_coeFn g).integral_compProd.aestronglyMeasurable
      (Eventually.of_forall fun h => (L1.integrable_coeFn h).integral_compProd) ?_
  simp_rw [← lintegral_fn_integral_sub (‖·‖ₑ) (L1.integrable_coeFn _) (L1.integrable_coeFn g)]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun i => zero_le) _
  · exact fun i => ∫⁻ x, ∫⁻ y, ‖i (x, y) - g (x, y)‖ₑ ∂η (a, x) ∂κ a
  swap; · exact fun i => lintegral_mono fun x => enorm_integral_le_lintegral_enorm _
  have (i : Lp (α := β × γ) E 1 (((κ otimesₖ η) a) : Measure (β × γ))) :
      Measurable fun z => ‖i z - g z‖ₑ :=
    ((Lp.stronglyMeasurable i).sub (Lp.stronglyMeasurable g)).enorm
  simp_rw [← lintegral_compProd _ _ _ (this _), ← L1.ofReal_norm_sub_eq_lintegral, ← ofReal_zero]
  refine (continuous_ofReal.tendsto 0).comp ?_
  rw [← tendsto_iff_norm_sub_tendsto_zero]
  exact tendsto_id

/--
theorem `integral_compProd` / 定理 `integral_compProd`

English:
theorem integral_compProd
  proof: by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE]
  apply Integrable.induction
  · intro c s hs h2s
    simp_rw [integral_indicator hs, ← indicator_comp_right, Function.comp_def,
      integral_indicator (measurable_prodMk_left hs), MeasureTheory.setIntegral_const,
      integral_smul

中文:
定理 integral_compProd
  证明: by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE]
  apply Integrable.induction
  · intro c s hs h2s
    simp_rw [integral_indicator hs, ← indicator_comp_right, Function.comp_def,
      integral_indicator (measurable_prodMk_left hs), MeasureTheory.setIntegral_const,
      integral_smul

Depends on / 依赖: CompleteSpace, Function, Function.comp_def, Integrable, Integrable.induction, Kernel, Kernel.compProd_apply, Kernel.measurable_kernel_prodMk_left, MeasureTheory, MeasureTheory.setIntegral_const, ae_kernel_lt_top, aemeasurable, compProd_apply, comp_def, h2s.ne, indicator_comp_right, integral, integral_indicator, integral_smul_const, integral_toReal
-/
theorem integral_compProd :
    forall {f : β × γ -> E} (_ : Integrable f ((κ otimesₖ η) a)),
      ∫ z, f z ∂(κ otimesₖ η) a = ∫ x, ∫ y, f (x, y) ∂η (a, x) ∂κ a := by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE]
  apply Integrable.induction
  · intro c s hs h2s
    simp_rw [integral_indicator hs, ← indicator_comp_right, Function.comp_def,
      integral_indicator (measurable_prodMk_left hs), MeasureTheory.setIntegral_const,
      integral_smul_const, measureReal_def]
    congr 1
    rw [integral_toReal]
    rotate_left
    · exact (Kernel.measurable_kernel_prodMk_left' hs _).aemeasurable
    · exact ae_kernel_lt_top a h2s.ne
    rw [Kernel.compProd_apply hs]
  · intro f g _ i_f i_g hf hg
    simp_rw [integral_add' i_f i_g, Kernel.integral_integral_add' i_f i_g, hf, hg]
  · exact isClosed_eq continuous_integral Kernel.continuous_integral_integral
  · intro f g hfg _ hf
    convert! hf using 1
    · exact integral_congr_ae hfg.symm
    · apply integral_congr_ae
      filter_upwards [ae_ae_of_ae_compProd hfg] with x hfgx using
        integral_congr_ae (ae_eq_symm hfgx)

/--
theorem `setIntegral_compProd` / 定理 `setIntegral_compProd`

English:
theorem setIntegral_compProd
  statement: {f : β × γ -> E} {s : Set β} {t : Set γ} (hs : MeasurableSet s)
  proof: by
  -- Porting note: `compProd_restrict` needed some explicit arguments
  rw [← Kernel.restrict_apply (κ otimesₖ η) (hs.prod ht)]; rw [← compProd_restrict hs ht]; rw [integral_compProd]
  · simp_rw [Kernel.restrict_apply]
  · rw [compProd_restrict, Kernel.restrict_apply]; exact hf

中文:
定理 setIntegral_compProd
  结论: {f : β × γ -> E} {s : Set β} {t : Set γ} (hs : MeasurableSet s)
  证明: by
  -- Porting note: `compProd_restrict` needed some explicit arguments
  rw [← Kernel.restrict_apply (κ otimesₖ η) (hs.prod ht)]; rw [← compProd_restrict hs ht]; rw [integral_compProd]
  · simp_rw [Kernel.restrict_apply]
  · rw [compProd_restrict, Kernel.restrict_apply]; exact hf
-/
theorem setIntegral_compProd {f : β × γ -> E} {s : Set β} {t : Set γ} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) ((κ otimesₖ η) a)) :
    ∫ z in s ×ˢ t, f z ∂(κ otimesₖ η) a = ∫ x in s, ∫ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  -- Porting note: `compProd_restrict` needed some explicit arguments
  rw [← Kernel.restrict_apply (κ otimesₖ η) (hs.prod ht)]; rw [← compProd_restrict hs ht]; rw [integral_compProd]
  · simp_rw [Kernel.restrict_apply]
  · rw [compProd_restrict, Kernel.restrict_apply]; exact hf

/--
theorem `setIntegral_compProd_univ_right` / 定理 `setIntegral_compProd_univ_right`

English:
theorem setIntegral_compProd_univ_right
  statement: (f : β × γ -> E) {s : Set β} (hs : MeasurableSet s)
  proof: by
  simp_rw [setIntegral_compProd hs MeasurableSet.univ hf, Measure.restrict_univ]

中文:
定理 setIntegral_compProd_univ_right
  结论: (f : β × γ -> E) {s : Set β} (hs : MeasurableSet s)
  证明: by
  simp_rw [setIntegral_compProd hs MeasurableSet.univ hf, Measure.restrict_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_univ, restrict_univ, setIntegral_compProd, simp_rw
-/
theorem setIntegral_compProd_univ_right (f : β × γ -> E) {s : Set β} (hs : MeasurableSet s)
    (hf : IntegrableOn f (s ×ˢ univ) ((κ otimesₖ η) a)) :
    ∫ z in s ×ˢ univ, f z ∂(κ otimesₖ η) a = ∫ x in s, ∫ y, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [setIntegral_compProd hs MeasurableSet.univ hf, Measure.restrict_univ]

/--
theorem `setIntegral_compProd_univ_left` / 定理 `setIntegral_compProd_univ_left`

English:
theorem setIntegral_compProd_univ_left
  statement: (f : β × γ -> E) {t : Set γ} (ht : MeasurableSet t)
  proof: by
  simp_rw [setIntegral_compProd MeasurableSet.univ ht hf, Measure.restrict_univ]

中文:
定理 setIntegral_compProd_univ_left
  结论: (f : β × γ -> E) {t : Set γ} (ht : MeasurableSet t)
  证明: by
  simp_rw [setIntegral_compProd MeasurableSet.univ ht hf, Measure.restrict_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_univ, restrict_univ, setIntegral_compProd, simp_rw
-/
theorem setIntegral_compProd_univ_left (f : β × γ -> E) {t : Set γ} (ht : MeasurableSet t)
    (hf : IntegrableOn f (univ ×ˢ t) ((κ otimesₖ η) a)) :
    ∫ z in univ ×ˢ t, f z ∂(κ otimesₖ η) a = ∫ x, ∫ y in t, f (x, y) ∂η (a, x) ∂κ a := by
  simp_rw [setIntegral_compProd MeasurableSet.univ ht hf, Measure.restrict_univ]

end compProd

section comp

variable {κ : Kernel α β} {η : Kernel β γ}

/--
theorem `_root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_comp` / 定理 `_root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_comp`

English:
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_comp
  statement: [NormedSpace Real E]
  proof: ⟨fun x => ∫ y, hf.mk f y ∂η x, hf.stronglyMeasurable_mk.integral_kernel, by
    filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩

中文:
定理 _root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_comp
  结论: [NormedSpace 实数 E]
  证明: ⟨fun x => ∫ y, hf.mk f y ∂η x, hf.stronglyMeasurable_mk.integral_kernel, by
    filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩

Depends on / 依赖: ae_ae_of_ae_comp, ae_eq_mk, filter_upwards, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk.integral_kernel, integral_congr_ae, integral_kernel, stronglyMeasurable_mk
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_comp [NormedSpace Real E]
    ⦃f : γ -> E⦄ (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
    AEStronglyMeasurable (fun x => ∫ y, f y ∂η x) (κ a) :=
  ⟨fun x => ∫ y, hf.mk f y ∂η x, hf.stronglyMeasurable_mk.integral_kernel, by
    filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk] with _ hx using integral_congr_ae hx⟩

/--
theorem `_root_.MeasureTheory.AEStronglyMeasurable.comp` / 定理 `_root_.MeasureTheory.AEStronglyMeasurable.comp`

English:
theorem _root_.MeasureTheory.AEStronglyMeasurable.comp
  statement: {δ : Type*} [TopologicalSpace δ]
  proof: by
  filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk] with x hx using
    ⟨hf.mk f, hf.stronglyMeasurable_mk, hx⟩

中文:
定理 _root_.MeasureTheory.AEStronglyMeasurable.comp
  结论: {δ : 类型} [TopologicalSpace δ]
  证明: by
  filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk] with x hx using
    ⟨hf.mk f, hf.stronglyMeasurable_mk, hx⟩

Depends on / 依赖: ae_ae_of_ae_comp, ae_eq_mk, filter_upwards, hf.ae_eq_mk, hf.mk, hf.stronglyMeasurable_mk, stronglyMeasurable_mk
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.comp {δ : Type*} [TopologicalSpace δ]
    {f : γ -> δ} (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
    forallᵐ x ∂κ a, AEStronglyMeasurable f (η x) := by
  filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk] with x hx using
    ⟨hf.mk f, hf.stronglyMeasurable_mk, hx⟩


/--
theorem `hasFiniteIntegral_comp_iff` / 定理 `hasFiniteIntegral_comp_iff`

English:
theorem hasFiniteIntegral_comp_iff
  given: ⦃f
  statement: γ -> E⦄ (hf : StronglyMeasurable f) :
  proof: by
  simp_rw [hasFiniteIntegral_iff_enorm, lintegral_comp _ _ _ hf.enorm]
  simp_rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => norm_nonneg _)
      hf.norm.aestronglyMeasurable, enorm_eq_ofReal toReal_nonneg, ofReal_norm]
  have : forall {p q r : Prop} (_ : r -> p), (r ↔ p ∧ q) ↔ p ->

中文:
定理 hasFiniteIntegral_comp_iff
  条件: ⦃f
  结论: γ -> E⦄ (hf : StronglyMeasurable f) :
  证明: by
  simp_rw [hasFiniteIntegral_iff_enorm, lintegral_comp _ _ _ hf.enorm]
  simp_rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => norm_nonneg _)
      hf.norm.aestronglyMeasurable, enorm_eq_ofReal toReal_nonneg, ofReal_norm]
  have : forall {p q r : Prop} (_ : r -> p), (r ↔ p ∧ q) ↔ p ->

Depends on / 依赖: ae_lt_top, ae_of_all, aestronglyMeasurable, and_congr_right_iff, and_iff_right_of_imp, enorm_eq_ofReal, filter_upwards, finiteness, hasFiniteIntegral_iff_enorm, hf.enorm, hf.norm.aestronglyMeasurable, integral_eq_lintegral_of_nonneg_ae, lintegral_comp, lintegral_congr_ae, norm_nonneg, ofReal_norm, ofReal_toReal, simp_rw, toReal_nonneg
-/
theorem hasFiniteIntegral_comp_iff ⦃f : γ -> E⦄ (hf : StronglyMeasurable f) :
    HasFiniteIntegral f ((η ∘ₖ κ) a) ↔
    (forallᵐ x ∂κ a, HasFiniteIntegral f (η x)) ∧ HasFiniteIntegral (fun x => ∫ y, ‖f y‖ ∂η x) (κ a) := by
  simp_rw [hasFiniteIntegral_iff_enorm, lintegral_comp _ _ _ hf.enorm]
  simp_rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => norm_nonneg _)
      hf.norm.aestronglyMeasurable, enorm_eq_ofReal toReal_nonneg, ofReal_norm]
  have : forall {p q r : Prop} (_ : r -> p), (r ↔ p ∧ q) ↔ p -> (r ↔ q) := fun h => by
    rw [← and_congr_right_iff]; rw [and_iff_right_of_imp h]
  rw [this]
  · intro h
    rw [lintegral_congr_ae]
    filter_upwards [h] with x hx
    rw [ofReal_toReal]
    finiteness
  · exact fun h => ae_lt_top hf.enorm.lintegral_kernel h.ne

/--
theorem `hasFiniteIntegral_comp_iff'` / 定理 `hasFiniteIntegral_comp_iff'`

English:
theorem hasFiniteIntegral_comp_iff'
  given: ⦃f
  statement: γ -> E⦄ (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
  proof: by
  rw [hasFiniteIntegral_congr hf.ae_eq_mk]; rw [hasFiniteIntegral_comp_iff hf.stronglyMeasurable_mk]
  refine and_congr (eventually_congr ?_) (hasFiniteIntegral_congr ?_)
  · filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk.symm] with _ hx using
      hasFiniteIntegral_congr hx
  · filter_upwards [ae

中文:
定理 hasFiniteIntegral_comp_iff'
  条件: ⦃f
  结论: γ -> E⦄ (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
  证明: by
  rw [hasFiniteIntegral_congr hf.ae_eq_mk]; rw [hasFiniteIntegral_comp_iff hf.stronglyMeasurable_mk]
  refine and_congr (eventually_congr ?_) (hasFiniteIntegral_congr ?_)
  · filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk.symm] with _ hx using
      hasFiniteIntegral_congr hx
  · filter_upwards [ae

Depends on / 依赖: EventuallyEq, EventuallyEq.fun_comp, ae_ae_of_ae_comp, ae_eq_mk, and_congr, eventually_congr, filter_upwards, fun_comp, hasFiniteIntegral_comp_iff, hasFiniteIntegral_congr, hf.ae_eq_mk, hf.ae_eq_mk.symm, hf.stronglyMeasurable_mk, integral_congr_ae, stronglyMeasurable_mk
-/
theorem hasFiniteIntegral_comp_iff' ⦃f : γ -> E⦄ (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
    HasFiniteIntegral f ((η ∘ₖ κ) a) ↔
    (forallᵐ x ∂κ a, HasFiniteIntegral f (η x)) ∧ HasFiniteIntegral (fun x => ∫ y, ‖f y‖ ∂η x) (κ a) := by
  rw [hasFiniteIntegral_congr hf.ae_eq_mk]; rw [hasFiniteIntegral_comp_iff hf.stronglyMeasurable_mk]
  refine and_congr (eventually_congr ?_) (hasFiniteIntegral_congr ?_)
  · filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk.symm] with _ hx using
      hasFiniteIntegral_congr hx
  · filter_upwards [ae_ae_of_ae_comp hf.ae_eq_mk.symm] with _ hx using
      integral_congr_ae (EventuallyEq.fun_comp hx _)

/--
theorem `integrable_comp_iff` / 定理 `integrable_comp_iff`

English:
theorem integrable_comp_iff
  given: ⦃f
  statement: γ -> E⦄ (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
  proof: by
  simp only [Integrable, hf, hasFiniteIntegral_comp_iff' hf, true_and, eventually_and, hf.comp,
    hf.norm.integral_kernel_comp]

中文:
定理 integrable_comp_iff
  条件: ⦃f
  结论: γ -> E⦄ (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
  证明: by
  simp only [Integrable, hf, hasFiniteIntegral_comp_iff' hf, true_and, eventually_and, hf.comp,
    hf.norm.integral_kernel_comp]

Depends on / 依赖: Integrable, eventually_and, hasFiniteIntegral_comp_iff, hf.comp, hf.norm.integral_kernel_comp, integral_kernel_comp, true_and
-/
theorem integrable_comp_iff ⦃f : γ -> E⦄ (hf : AEStronglyMeasurable f ((η ∘ₖ κ) a)) :
    Integrable f ((η ∘ₖ κ) a) ↔
    (forallᵐ y ∂κ a, Integrable f (η y)) ∧ Integrable (fun y => ∫ z, ‖f z‖ ∂η y) (κ a) := by
  simp only [Integrable, hf, hasFiniteIntegral_comp_iff' hf, true_and, eventually_and, hf.comp,
    hf.norm.integral_kernel_comp]

/--
lemma `_root_.MeasureTheory.Measure.integrable_comp_iff` / 引理 `_root_.MeasureTheory.Measure.integrable_comp_iff`

English:
lemma _root_.MeasureTheory.Measure.integrable_comp_iff
  statement: {μ : Measure α} {f : β -> E}
  proof: by
  rw [Measure.comp_eq_comp_const_apply]; rw [ProbabilityTheory.integrable_comp_iff]
  · simp
  · simpa [Kernel.comp_apply]

中文:
引理 _root_.MeasureTheory.Measure.integrable_comp_iff
  结论: {μ : Measure α} {f : β -> E}
  证明: by
  rw [Measure.comp_eq_comp_const_apply]; rw [ProbabilityTheory.integrable_comp_iff]
  · simp
  · simpa [Kernel.comp_apply]
-/
protected lemma _root_.MeasureTheory.Measure.integrable_comp_iff {μ : Measure α} {f : β -> E}
    (hf : AEStronglyMeasurable f (κ ∘ₘ μ)) :
    Integrable f (κ ∘ₘ μ)
      ↔ (forallᵐ x ∂μ, Integrable f (κ x)) ∧ Integrable (fun x => ∫ y, ‖f y‖ ∂κ x) μ := by
  rw [Measure.comp_eq_comp_const_apply]; rw [ProbabilityTheory.integrable_comp_iff]
  · simp
  · simpa [Kernel.comp_apply]

/--
theorem `_root_.MeasureTheory.Integrable.ae_of_comp` / 定理 `_root_.MeasureTheory.Integrable.ae_of_comp`

English:
theorem _root_.MeasureTheory.Integrable.ae_of_comp
  given: ⦃f
  statement: γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a)) :
  proof: ((integrable_comp_iff hf.1).1 hf).1

中文:
定理 _root_.MeasureTheory.Integrable.ae_of_comp
  条件: ⦃f
  结论: γ -> E⦄ (hf : 整数egrable f ((η ∘ₖ κ) a)) :
  证明: ((integrable_comp_iff hf.1).1 hf).1

Depends on / 依赖: integrable_comp_iff
-/
theorem _root_.MeasureTheory.Integrable.ae_of_comp ⦃f : γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a)) :
    forallᵐ x ∂κ a, Integrable f (η x) := ((integrable_comp_iff hf.1).1 hf).1

/--
theorem `_root_.MeasureTheory.Integrable.integral_norm_comp` / 定理 `_root_.MeasureTheory.Integrable.integral_norm_comp`

English:
theorem _root_.MeasureTheory.Integrable.integral_norm_comp
  given: ⦃f
  statement: γ -> E⦄
  proof: ((integrable_comp_iff hf.1).1 hf).2

中文:
定理 _root_.MeasureTheory.Integrable.integral_norm_comp
  条件: ⦃f
  结论: γ -> E⦄
  证明: ((integrable_comp_iff hf.1).1 hf).2

Depends on / 依赖: integrable_comp_iff
-/
theorem _root_.MeasureTheory.Integrable.integral_norm_comp ⦃f : γ -> E⦄
    (hf : Integrable f ((η ∘ₖ κ) a)) : Integrable (fun x => ∫ y, ‖f y‖ ∂η x) (κ a) :=
  ((integrable_comp_iff hf.1).1 hf).2

/--
theorem `_root_.MeasureTheory.Integrable.integral_comp` / 定理 `_root_.MeasureTheory.Integrable.integral_comp`

English:
theorem _root_.MeasureTheory.Integrable.integral_comp
  given: [NormedSpace Real E] ⦃f
  statement: γ -> E⦄
  proof: Integrable.mono hf.integral_norm_comp hf.1.integral_kernel_comp
    ae_of_all _ fun _ => (norm_integral_le_integral_norm _).trans_eq
    (norm_of_nonneg <| integral_nonneg_of_ae <| ae_of_all _ fun _ => norm_nonneg _).symm

中文:
定理 _root_.MeasureTheory.Integrable.integral_comp
  条件: [NormedSpace 实数 E] ⦃f
  结论: γ -> E⦄
  证明: Integrable.mono hf.integral_norm_comp hf.1.integral_kernel_comp
    ae_of_all _ fun _ => (norm_integral_le_integral_norm _).trans_eq
    (norm_of_nonneg <| integral_nonneg_of_ae <| ae_of_all _ fun _ => norm_nonneg _).symm

Depends on / 依赖: Integrable, Integrable.mono, ae_of_all, hf.integral_norm_comp, integral_kernel_comp, integral_nonneg_of_ae, integral_norm_comp, norm_integral_le_integral_norm, norm_nonneg, norm_of_nonneg, trans_eq
-/
theorem _root_.MeasureTheory.Integrable.integral_comp [NormedSpace Real E] ⦃f : γ -> E⦄
    (hf : Integrable f ((η ∘ₖ κ) a)) : Integrable (fun x => ∫ y, f y ∂η x) (κ a) :=
Integrable.mono hf.integral_norm_comp hf.1.integral_kernel_comp
    ae_of_all _ fun _ => (norm_integral_le_integral_norm _).trans_eq
    (norm_of_nonneg <| integral_nonneg_of_ae <| ae_of_all _ fun _ => norm_nonneg _).symm

/-! ### Bochner integral with respect to the composition -/

variable [NormedSpace Real E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace Real E']

namespace Kernel

/--
theorem `integral_fn_integral_add_comp` / 定理 `integral_fn_integral_add_comp`

English:
theorem integral_fn_integral_add_comp
  given: ⦃f g
  statement: γ -> E⦄ (F : E -> E')
  proof: by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_comp, hg.ae_of_comp] with _ h2f h2g
  simp [integral_add h2f h2g]

中文:
定理 integral_fn_integral_add_comp
  条件: ⦃f g
  结论: γ -> E⦄ (F : E -> E')
  证明: by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_comp, hg.ae_of_comp] with _ h2f h2g
  simp [integral_add h2f h2g]

Depends on / 依赖: ae_of_comp, filter_upwards, hf.ae_of_comp, hg.ae_of_comp, integral_add, integral_congr_ae
-/
theorem integral_fn_integral_add_comp ⦃f g : γ -> E⦄ (F : E -> E')
    (hf : Integrable f ((η ∘ₖ κ) a)) (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, F (∫ y, f y + g y ∂η x) ∂κ a = ∫ x, F (∫ y, f y ∂η x + ∫ y, g y ∂η x) ∂κ a := by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_comp, hg.ae_of_comp] with _ h2f h2g
  simp [integral_add h2f h2g]

/--
theorem `integral_fn_integral_sub_comp` / 定理 `integral_fn_integral_sub_comp`

English:
theorem integral_fn_integral_sub_comp
  given: ⦃f g
  statement: γ -> E⦄ (F : E -> E')
  proof: by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_comp, hg.ae_of_comp] with _ h2f h2g
  simp [integral_sub h2f h2g]

中文:
定理 integral_fn_integral_sub_comp
  条件: ⦃f g
  结论: γ -> E⦄ (F : E -> E')
  证明: by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_comp, hg.ae_of_comp] with _ h2f h2g
  simp [integral_sub h2f h2g]

Depends on / 依赖: ae_of_comp, filter_upwards, hf.ae_of_comp, hg.ae_of_comp, integral_congr_ae, integral_sub
-/
theorem integral_fn_integral_sub_comp ⦃f g : γ -> E⦄ (F : E -> E')
    (hf : Integrable f ((η ∘ₖ κ) a)) (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, F (∫ y, f y - g y ∂η x) ∂κ a = ∫ x, F (∫ y, f y ∂η x - ∫ y, g y ∂η x) ∂κ a := by
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_of_comp, hg.ae_of_comp] with _ h2f h2g
  simp [integral_sub h2f h2g]

/--
theorem `lintegral_fn_integral_sub_comp` / 定理 `lintegral_fn_integral_sub_comp`

English:
theorem lintegral_fn_integral_sub_comp
  given: ⦃f g
  statement: γ -> E⦄ (F : E -> Real>=0∞)
  proof: by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.ae_of_comp, hg.ae_of_comp] with _ h2f h2g
  simp [integral_sub h2f h2g]

中文:
定理 lintegral_fn_integral_sub_comp
  条件: ⦃f g
  结论: γ -> E⦄ (F : E -> 实数>=0∞)
  证明: by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.ae_of_comp, hg.ae_of_comp] with _ h2f h2g
  simp [integral_sub h2f h2g]

Depends on / 依赖: ae_of_comp, filter_upwards, hf.ae_of_comp, hg.ae_of_comp, integral_sub, lintegral_congr_ae
-/
theorem lintegral_fn_integral_sub_comp ⦃f g : γ -> E⦄ (F : E -> Real>=0∞)
    (hf : Integrable f ((η ∘ₖ κ) a)) (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫⁻ x, F (∫ y, f y - g y ∂η x) ∂κ a = ∫⁻ x, F (∫ y, f y ∂η x - ∫ y, g y ∂η x) ∂κ a := by
  refine lintegral_congr_ae ?_
  filter_upwards [hf.ae_of_comp, hg.ae_of_comp] with _ h2f h2g
  simp [integral_sub h2f h2g]

/--
theorem `integral_integral_add_comp` / 定理 `integral_integral_add_comp`

English:
theorem integral_integral_add_comp
  given: ⦃f g
  statement: γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
  proof: (integral_fn_integral_add_comp id hf hg).trans integral_add hf.integral_comp hg.integral_comp

中文:
定理 integral_integral_add_comp
  条件: ⦃f g
  结论: γ -> E⦄ (hf : 整数egrable f ((η ∘ₖ κ) a))
  证明: (integral_fn_integral_add_comp id hf hg).trans integral_add hf.integral_comp hg.integral_comp

Depends on / 依赖: hf.integral_comp, hg.integral_comp, integral_add, integral_comp, integral_fn_integral_add_comp
-/
theorem integral_integral_add_comp ⦃f g : γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
    (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, ∫ y, f y + g y ∂η x ∂κ a = ∫ x, ∫ y, f y ∂η x ∂κ a + ∫ x, ∫ y, g y ∂η x ∂κ a :=
(integral_fn_integral_add_comp id hf hg).trans integral_add hf.integral_comp hg.integral_comp

/--
theorem `integral_integral_add'_comp` / 定理 `integral_integral_add'_comp`

English:
theorem integral_integral_add'_comp
  given: ⦃f g
  statement: γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
  proof: integral_integral_add_comp hf hg

中文:
定理 integral_integral_add'_comp
  条件: ⦃f g
  结论: γ -> E⦄ (hf : 整数egrable f ((η ∘ₖ κ) a))
  证明: integral_integral_add_comp hf hg

Depends on / 依赖: integral_integral_add_comp
-/
theorem integral_integral_add'_comp ⦃f g : γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
    (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, ∫ y, (f + g) y ∂η x ∂κ a = ∫ x, ∫ y, f y ∂η x ∂κ a + ∫ x, ∫ y, g y ∂η x ∂κ a :=
  integral_integral_add_comp hf hg

/--
theorem `integral_integral_sub_comp` / 定理 `integral_integral_sub_comp`

English:
theorem integral_integral_sub_comp
  given: ⦃f g
  statement: γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
  proof: (integral_fn_integral_sub_comp id hf hg).trans integral_sub hf.integral_comp hg.integral_comp

中文:
定理 integral_integral_sub_comp
  条件: ⦃f g
  结论: γ -> E⦄ (hf : 整数egrable f ((η ∘ₖ κ) a))
  证明: (integral_fn_integral_sub_comp id hf hg).trans integral_sub hf.integral_comp hg.integral_comp

Depends on / 依赖: hf.integral_comp, hg.integral_comp, integral_comp, integral_fn_integral_sub_comp, integral_sub
-/
theorem integral_integral_sub_comp ⦃f g : γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
    (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, ∫ y, f y - g y ∂η x ∂κ a = ∫ x, ∫ y, f y ∂η x ∂κ a - ∫ x, ∫ y, g y ∂η x ∂κ a :=
(integral_fn_integral_sub_comp id hf hg).trans integral_sub hf.integral_comp hg.integral_comp

/--
theorem `integral_integral_sub'_comp` / 定理 `integral_integral_sub'_comp`

English:
theorem integral_integral_sub'_comp
  given: ⦃f g
  statement: γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
  proof: integral_integral_sub_comp hf hg

中文:
定理 integral_integral_sub'_comp
  条件: ⦃f g
  结论: γ -> E⦄ (hf : 整数egrable f ((η ∘ₖ κ) a))
  证明: integral_integral_sub_comp hf hg

Depends on / 依赖: integral_integral_sub_comp
-/
theorem integral_integral_sub'_comp ⦃f g : γ -> E⦄ (hf : Integrable f ((η ∘ₖ κ) a))
    (hg : Integrable g ((η ∘ₖ κ) a)) :
    ∫ x, ∫ y, (f - g) y ∂η x ∂κ a = ∫ x, ∫ y, f y ∂η x ∂κ a - ∫ x, ∫ y, g y ∂η x ∂κ a :=
  integral_integral_sub_comp hf hg

/--
theorem `continuous_integral_integral_comp` / 定理 `continuous_integral_integral_comp`

English:
theorem continuous_integral_integral_comp
  proof: by
  refine continuous_iff_continuousAt.2 fun g => ?_
  refine tendsto_integral_of_L1 _ (L1.integrable_coeFn g).integral_comp.aestronglyMeasurable
      (Eventually.of_forall fun h => (L1.integrable_coeFn h).integral_comp) ?_
  simp_rw [← lintegral_fn_integral_sub_comp (‖·‖ₑ) (L1.integrable_coeFn _)

中文:
定理 continuous_integral_integral_comp
  证明: by
  refine continuous_iff_continuousAt.2 fun g => ?_
  refine tendsto_integral_of_L1 _ (L1.integrable_coeFn g).integral_comp.aestronglyMeasurable
      (Eventually.of_forall fun h => (L1.integrable_coeFn h).integral_comp) ?_
  simp_rw [← lintegral_fn_integral_sub_comp (‖·‖ₑ) (L1.integrable_coeFn _)

Depends on / 依赖: Eventually, Eventually.of_forall, L1.integrable_coeFn, aestronglyMeasurable, continuous_iff_continuousAt, integrable_coeFn, integral_comp, integral_comp.aestronglyMeasurable, lintegral_fn_integral_sub_comp, lintegral_mono, of_forall, simp_rw, tendsto_const_nhds, tendsto_integral_of_L1, tendsto_of_tendsto_of_tendsto_of_le_of_le, zero_le
-/
theorem continuous_integral_integral_comp :
    Continuous fun f : γ ->₁[(η ∘ₖ κ) a] E => ∫ x, ∫ y, f y ∂η x ∂κ a := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  refine tendsto_integral_of_L1 _ (L1.integrable_coeFn g).integral_comp.aestronglyMeasurable
      (Eventually.of_forall fun h => (L1.integrable_coeFn h).integral_comp) ?_
  simp_rw [← lintegral_fn_integral_sub_comp (‖·‖ₑ) (L1.integrable_coeFn _) (L1.integrable_coeFn g)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (h := fun i => ∫⁻ x, ∫⁻ y, ‖i y - g y‖ₑ ∂η x ∂κ a)
    tendsto_const_nhds ?_ (fun _ => zero_le) ?_
  swap; · exact fun _ => lintegral_mono fun _ => enorm_integral_le_lintegral_enorm _
  have (i : γ ->₁[(η ∘ₖ κ) a] E) : Measurable fun z => ‖i z - g z‖ₑ :=
    ((Lp.stronglyMeasurable i).sub (Lp.stronglyMeasurable g)).enorm
  simp_rw [← lintegral_comp _ _ _ (this _), ← L1.ofReal_norm_sub_eq_lintegral, ← ofReal_zero]
  exact (continuous_ofReal.tendsto 0).comp (tendsto_iff_norm_sub_tendsto_zero.1 tendsto_id)

/--
theorem `integral_comp` / 定理 `integral_comp`

English:
theorem integral_comp
  statement: forall {f : γ -> E} (_ : Integrable f ((η ∘ₖ κ) a)),
  proof: by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE]
  apply Integrable.induction
  · intro c s hs ms
    simp_rw [integral_indicator hs, MeasureTheory.setIntegral_const, integral_smul_const,
      measureReal_def]
    congr
    rw [integral_toReal]; rw [Kernel.comp_apply' _ _ _ hs]
    

中文:
定理 integral_comp
  结论: 对任意 {f : γ -> E} (_ : 整数egrable f ((η ∘ₖ κ) a)),
  证明: by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE]
  apply Integrable.induction
  · intro c s hs ms
    simp_rw [integral_indicator hs, MeasureTheory.setIntegral_const, integral_smul_const,
      measureReal_def]
    congr
    rw [integral_toReal]; rw [Kernel.comp_apply' _ _ _ hs]
    

Depends on / 依赖: CompleteSpace, Integrable, Integrable.induction, Kernel, Kernel.comp_apply, Kernel.measurable_coe, MeasureTheory, MeasureTheory.setIntegral_const, _comp, ae_lt_top_of_comp_ne_top, aemeasurable, comp_apply, continuous_in, integral, integral_add, integral_indicator, integral_integral_add, integral_smul_const, integral_toReal, isClosed_eq
-/
theorem integral_comp : forall {f : γ -> E} (_ : Integrable f ((η ∘ₖ κ) a)),
    ∫ z, f z ∂(η ∘ₖ κ) a = ∫ x, ∫ y, f y ∂η x ∂κ a := by
  by_cases hE : CompleteSpace E; swap
  · simp [integral, hE]
  apply Integrable.induction
  · intro c s hs ms
    simp_rw [integral_indicator hs, MeasureTheory.setIntegral_const, integral_smul_const,
      measureReal_def]
    congr
    rw [integral_toReal]; rw [Kernel.comp_apply' _ _ _ hs]
    · exact (Kernel.measurable_coe _ hs).aemeasurable
    · exact ae_lt_top_of_comp_ne_top a ms.ne
  · rintro f g - i_f i_g hf hg
    simp_rw [integral_add' i_f i_g, integral_integral_add'_comp i_f i_g, hf, hg]
  · exact isClosed_eq continuous_integral Kernel.continuous_integral_integral_comp
  · rintro f g hfg - hf
    convert! hf using 1
    · exact integral_congr_ae hfg.symm
    · apply integral_congr_ae
      filter_upwards [ae_ae_of_ae_comp hfg] with x hfgx using integral_congr_ae (ae_eq_symm hfgx)

/--
theorem `setIntegral_comp` / 定理 `setIntegral_comp`

English:
theorem setIntegral_comp
  statement: {f : γ -> E} {s : Set γ} (hs : MeasurableSet s)
  proof: by
  rw [← restrict_apply (η ∘ₖ κ) hs]; rw [← comp_restrict hs]; rw [integral_comp]
  · simp_rw [restrict_apply]
  · rwa [comp_restrict, restrict_apply]

中文:
定理 setIntegral_comp
  结论: {f : γ -> E} {s : Set γ} (hs : MeasurableSet s)
  证明: by
  rw [← restrict_apply (η ∘ₖ κ) hs]; rw [← comp_restrict hs]; rw [integral_comp]
  · simp_rw [restrict_apply]
  · rwa [comp_restrict, restrict_apply]

Depends on / 依赖: comp_restrict, integral_comp, restrict_apply, simp_rw
-/
theorem setIntegral_comp {f : γ -> E} {s : Set γ} (hs : MeasurableSet s)
    (hf : IntegrableOn f s ((η ∘ₖ κ) a)) :
    ∫ z in s, f z ∂(η ∘ₖ κ) a = ∫ x, ∫ y in s, f y ∂η x ∂κ a := by
  rw [← restrict_apply (η ∘ₖ κ) hs]; rw [← comp_restrict hs]; rw [integral_comp]
  · simp_rw [restrict_apply]
  · rwa [comp_restrict, restrict_apply]

end Kernel

end comp

end ProbabilityTheory

namespace MeasureTheory

namespace Measure

variable {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [NormedAddCommGroup E] {a : α} {κ : Kernel α β} {μ : Measure α} {f : β -> E}

section Integral

/--
lemma `_root_.MeasureTheory.AEStronglyMeasurable.ae_of_compProd` / 引理 `_root_.MeasureTheory.AEStronglyMeasurable.ae_of_compProd`

English:
lemma _root_.MeasureTheory.AEStronglyMeasurable.ae_of_compProd
  statement: [SFinite μ] [IsSFiniteKernel κ]
  proof: by
  simpa using hf.compProd_mk_left

中文:
引理 _root_.MeasureTheory.AEStronglyMeasurable.ae_of_compProd
  结论: [SFinite μ] [IsSFiniteKernel κ]
  证明: by
  simpa using hf.compProd_mk_left

Depends on / 依赖: compProd_mk_left, hf.compProd_mk_left
-/
lemma _root_.MeasureTheory.AEStronglyMeasurable.ae_of_compProd [SFinite μ] [IsSFiniteKernel κ]
    {E : Type*} [NormedAddCommGroup E] {f : α -> β -> E}
    (hf : AEStronglyMeasurable f.uncurry (μ otimesₘ κ)) :
    forallᵐ x ∂μ, AEStronglyMeasurable (f x) (κ x) := by
  simpa using hf.compProd_mk_left

/--
lemma `integrable_compProd_iff` / 引理 `integrable_compProd_iff`

English:
lemma integrable_compProd_iff
  statement: [SFinite μ] [IsSFiniteKernel κ] {E : Type*} [NormedAddCommGroup E]
  proof: by
  simp_rw [Measure.compProd, ProbabilityTheory.integrable_compProd_iff hf, Kernel.prodMkLeft_apply,
    Kernel.const_apply]

中文:
引理 integrable_compProd_iff
  结论: [SFinite μ] [IsSFiniteKernel κ] {E : 类型} [NormedAddCommGroup E]
  证明: by
  simp_rw [Measure.compProd, ProbabilityTheory.integrable_compProd_iff hf, Kernel.prodMkLeft_apply,
    Kernel.const_apply]

Depends on / 依赖: Kernel, Kernel.const_apply, Kernel.prodMkLeft_apply, Measure, Measure.compProd, ProbabilityTheory, ProbabilityTheory.integrable_compProd_iff, compProd, const_apply, integrable_compProd_iff, prodMkLeft_apply, simp_rw
-/
lemma integrable_compProd_iff [SFinite μ] [IsSFiniteKernel κ] {E : Type*} [NormedAddCommGroup E]
    {f : α × β -> E} (hf : AEStronglyMeasurable f (μ otimesₘ κ)) :
    Integrable f (μ otimesₘ κ) ↔
      (forallᵐ x ∂μ, Integrable (fun y => f (x, y)) (κ x)) ∧
        Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂(κ x)) μ := by
  simp_rw [Measure.compProd, ProbabilityTheory.integrable_compProd_iff hf, Kernel.prodMkLeft_apply,
    Kernel.const_apply]

/--
lemma `integral_compProd` / 引理 `integral_compProd`

English:
lemma integral_compProd
  statement: [SFinite μ] [IsSFiniteKernel κ] {E : Type*}
  proof: by
  rw [Measure.compProd]; rw [ProbabilityTheory.integral_compProd hf]
  simp

中文:
引理 integral_compProd
  结论: [SFinite μ] [IsSFiniteKernel κ] {E : 类型}
  证明: by
  rw [Measure.compProd]; rw [ProbabilityTheory.integral_compProd hf]
  simp

Depends on / 依赖: Measure, Measure.compProd, ProbabilityTheory, ProbabilityTheory.integral_compProd, compProd, integral_compProd
-/
lemma integral_compProd [SFinite μ] [IsSFiniteKernel κ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    {f : α × β -> E} (hf : Integrable f (μ otimesₘ κ)) :
    ∫ x, f x ∂(μ otimesₘ κ) = ∫ a, ∫ b, f (a, b) ∂(κ a) ∂μ := by
  rw [Measure.compProd]; rw [ProbabilityTheory.integral_compProd hf]
  simp

/--
lemma `setIntegral_compProd` / 引理 `setIntegral_compProd`

English:
lemma setIntegral_compProd
  statement: [SFinite μ] [IsSFiniteKernel κ] {E : Type*}
  proof: by
  rw [Measure.compProd]; rw [ProbabilityTheory.setIntegral_compProd hs ht hf]
  simp

中文:
引理 setIntegral_compProd
  结论: [SFinite μ] [IsSFiniteKernel κ] {E : 类型}
  证明: by
  rw [Measure.compProd]; rw [ProbabilityTheory.setIntegral_compProd hs ht hf]
  simp

Depends on / 依赖: Measure, Measure.compProd, ProbabilityTheory, ProbabilityTheory.setIntegral_compProd, compProd, setIntegral_compProd
-/
lemma setIntegral_compProd [SFinite μ] [IsSFiniteKernel κ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t)
    {f : α × β -> E} (hf : IntegrableOn f (s ×ˢ t) (μ otimesₘ κ)) :
    ∫ x in s ×ˢ t, f x ∂(μ otimesₘ κ) = ∫ a in s, ∫ b in t, f (a, b) ∂(κ a) ∂μ := by
  rw [Measure.compProd]; rw [ProbabilityTheory.setIntegral_compProd hs ht hf]
  simp

end Integral

section Integrable

/--
lemma `integrable_compProd_snd_iff` / 引理 `integrable_compProd_snd_iff`

English:
lemma integrable_compProd_snd_iff
  statement: [SFinite μ] [IsSFiniteKernel κ]
  proof: by
  rw [← Measure.snd_compProd]; rw [Measure.snd]; rw [integrable_map_measure _ measurable_snd.aemeasurable]; rw [Function.comp_def]
  rwa [← Measure.snd, Measure.snd_compProd]

中文:
引理 integrable_compProd_snd_iff
  结论: [SFinite μ] [IsSFiniteKernel κ]
  证明: by
  rw [← Measure.snd_compProd]; rw [Measure.snd]; rw [integrable_map_measure _ measurable_snd.aemeasurable]; rw [Function.comp_def]
  rwa [← Measure.snd, Measure.snd_compProd]

Depends on / 依赖: Function, Function.comp_def, Measure, Measure.snd, Measure.snd_compProd, aemeasurable, comp_def, integrable_map_measure, measurable_snd, measurable_snd.aemeasurable, snd_compProd
-/
lemma integrable_compProd_snd_iff [SFinite μ] [IsSFiniteKernel κ]
    (hf : AEStronglyMeasurable f (κ ∘ₘ μ)) :
    Integrable (fun p => f p.2) (μ otimesₘ κ) ↔ Integrable f (κ ∘ₘ μ) := by
  rw [← Measure.snd_compProd]; rw [Measure.snd]; rw [integrable_map_measure _ measurable_snd.aemeasurable]; rw [Function.comp_def]
  rwa [← Measure.snd, Measure.snd_compProd]

/--
lemma `ae_integrable_of_integrable_comp` / 引理 `ae_integrable_of_integrable_comp`

English:
lemma ae_integrable_of_integrable_comp
  given: (h_int : Integrable f (κ ∘ₘ μ))
  proof: by
  rw [Measure.comp_eq_comp_const_apply]; rw [integrable_comp_iff h_int.1] at h_int
  exact h_int.1

中文:
引理 ae_integrable_of_integrable_comp
  条件: (h_int : 整数egrable f (κ ∘ₘ μ))
  证明: by
  rw [Measure.comp_eq_comp_const_apply]; rw [integrable_comp_iff h_int.1] at h_int
  exact h_int.1

Depends on / 依赖: Measure, Measure.comp_eq_comp_const_apply, comp_eq_comp_const_apply, h_int, integrable_comp_iff
-/
lemma ae_integrable_of_integrable_comp (h_int : Integrable f (κ ∘ₘ μ)) :
    forallᵐ x ∂μ, Integrable f (κ x) := by
  rw [Measure.comp_eq_comp_const_apply]; rw [integrable_comp_iff h_int.1] at h_int
  exact h_int.1

/--
lemma `integrable_integral_norm_of_integrable_comp` / 引理 `integrable_integral_norm_of_integrable_comp`

English:
lemma integrable_integral_norm_of_integrable_comp
  given: (h_int : Integrable f (κ ∘ₘ μ))
  proof: by
  rw [Measure.comp_eq_comp_const_apply]; rw [integrable_comp_iff h_int.1] at h_int
  exact h_int.2

中文:
引理 integrable_integral_norm_of_integrable_comp
  条件: (h_int : 整数egrable f (κ ∘ₘ μ))
  证明: by
  rw [Measure.comp_eq_comp_const_apply]; rw [integrable_comp_iff h_int.1] at h_int
  exact h_int.2

Depends on / 依赖: Measure, Measure.comp_eq_comp_const_apply, comp_eq_comp_const_apply, h_int, integrable_comp_iff
-/
lemma integrable_integral_norm_of_integrable_comp (h_int : Integrable f (κ ∘ₘ μ)) :
    Integrable (fun x => ∫ y, ‖f y‖ ∂κ x) μ := by
  rw [Measure.comp_eq_comp_const_apply]; rw [integrable_comp_iff h_int.1] at h_int
  exact h_int.2

end Integrable

end Measure

end MeasureTheory
