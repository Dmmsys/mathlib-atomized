/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!

# Vector measure defined by an integral

Given a measure `μ` and an integrable function `f : α → E`, we can define a vector measure `v` such
that for all measurable sets `s`, `v s = ∫ x in s, f x ∂μ`. This definition is useful for
the Radon-Nikodym theorem for signed measures.

## Main definitions

* `MeasureTheory.Measure.withDensityᵥ`: the vector measure formed by integrating a function `f`
  with respect to a measure `μ` on some set if `f` is integrable, and `0` otherwise.

-/

@[expose] public section


noncomputable section

open scoped MeasureTheory NNReal ENNReal

variable {α : Type*} {m : MeasurableSpace α}

namespace MeasureTheory

open TopologicalSpace

variable {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

open scoped Classical in
/--
Definition of `Measure.withDensityᵥ` / `Measure.withDensityᵥ` 的定义

English:
definition Measure.withDensityᵥ
  signature: {m : MeasurableSpace α} (μ : Measure α) (f : α -> E)
  body: if hf : Integrable f μ then
    { measureOf' := fun s => if MeasurableSet s then ∫ x in s, f x ∂μ else 0
      empty' := by simp
      not_measurable' := fun _ hs => if_neg hs
      m_iUnion' := fun s hs₁ hs₂ => by
        convert! hasSum_integral_iUnion hs₁ hs₂ hf.integrableOn with n
        · rw [

中文:
定义 测度.withDensityᵥ
  签名: {m : 可测空间 α} (μ : 测度 α) (f : α -> E)
  定义体: if hf : Integrable f μ then
    { measureOf' := fun s => if MeasurableSet s then ∫ x in s, f x ∂μ else 0
      empty' := by simp
      not_measurable' := fun _ hs => if_neg hs
      m_iUnion' := fun s hs₁ hs₂ => by
        convert! hasSum_integral_iUnion hs₁ hs₂ hf.integrableOn with n
        · rw [

Depends on / 依赖: Integrable, MeasurableSet, MeasurableSet.iUnion, convert, hasSum_integral_iUnion, hf.integrableOn, iUnion, if_neg, if_pos, integrableOn, m_iUnion, measureOf, not_measurable
-/
def Measure.withDensityᵥ {m : MeasurableSpace α} (μ : Measure α) (f : α -> E) : VectorMeasure α E :=
  if hf : Integrable f μ then
    { measureOf' := fun s => if MeasurableSet s then ∫ x in s, f x ∂μ else 0
      empty' := by simp
      not_measurable' := fun _ hs => if_neg hs
      m_iUnion' := fun s hs₁ hs₂ => by
        convert! hasSum_integral_iUnion hs₁ hs₂ hf.integrableOn with n
        · rw [if_pos (hs₁ n)]
        · rw [if_pos (MeasurableSet.iUnion hs₁)] }
  else 0

open Measure

variable {f g : α -> E}

/--
theorem `withDensityᵥ_apply` / 定理 `withDensityᵥ_apply`

English:
theorem withDensityᵥ_apply
  given: (hf : Integrable f μ) {s : Set α} (hs : MeasurableSet s)
  proof: by rw [withDensityᵥ, dif_pos hf]; exact dif_pos hs

@[simp]

中文:
定理 withDensityᵥ_apply
  条件: (hf : 可积 f μ) {s : 集合 α} (hs : 可测集 s)
  证明: by rw [withDensityᵥ, dif_pos hf]; exact dif_pos hs

@[simp]

Depends on / 依赖: dif_pos
-/
theorem withDensityᵥ_apply (hf : Integrable f μ) {s : Set α} (hs : MeasurableSet s) :
    μ.withDensityᵥ f s = ∫ x in s, f x ∂μ := by rw [withDensityᵥ, dif_pos hf]; exact dif_pos hs

@[simp]
/--
theorem `withDensityᵥ_zero` / 定理 `withDensityᵥ_zero`

English:
theorem withDensityᵥ_zero
  statement: μ.withDensityᵥ (0 : α -> E) = 0
  proof: by
  ext1 s hs
  rw [withDensityᵥ_apply (integrable_zero α E μ) hs]
  simp

@[simp]

中文:
定理 withDensityᵥ_zero
  结论: μ.withDensityᵥ (0 : α -> E) = 0
  证明: by
  ext1 s hs
  rw [withDensityᵥ_apply (integrable_zero α E μ) hs]
  simp

@[simp]

Depends on / 依赖: integrable_zero
-/
theorem withDensityᵥ_zero : μ.withDensityᵥ (0 : α -> E) = 0 := by
  ext1 s hs
  rw [withDensityᵥ_apply (integrable_zero α E μ) hs]
  simp

@[simp]
/--
theorem `withDensityᵥ_neg` / 定理 `withDensityᵥ_neg`

English:
theorem withDensityᵥ_neg
  statement: μ.withDensityᵥ (-f) = -μ.withDensityᵥ f
  proof: by
  by_cases hf : Integrable f μ
  · ext1 i hi
    rw [_root_.neg_apply]; rw [withDensityᵥ_apply hf hi]; rw [← integral_neg]; rw [withDensityᵥ_apply hf.neg hi]
    simp only [Pi.neg_apply]
  · rw [withDensityᵥ, withDensityᵥ, dif_neg hf, dif_neg, neg_zero]
    rwa [integrable_neg_iff]

中文:
定理 withDensityᵥ_neg
  结论: μ.withDensityᵥ (-f) = -μ.withDensityᵥ f
  证明: by
  by_cases hf : Integrable f μ
  · ext1 i hi
    rw [_root_.neg_apply]; rw [withDensityᵥ_apply hf hi]; rw [← integral_neg]; rw [withDensityᵥ_apply hf.neg hi]
    simp only [Pi.neg_apply]
  · rw [withDensityᵥ, withDensityᵥ, dif_neg hf, dif_neg, neg_zero]
    rwa [integrable_neg_iff]

Depends on / 依赖: Integrable, Pi.neg_apply, _root_, _root_.neg_apply, dif_neg, hf.neg, integrable_neg_iff, integral_neg, neg_apply, neg_zero
-/
theorem withDensityᵥ_neg : μ.withDensityᵥ (-f) = -μ.withDensityᵥ f := by
  by_cases hf : Integrable f μ
  · ext1 i hi
    rw [_root_.neg_apply]; rw [withDensityᵥ_apply hf hi]; rw [← integral_neg]; rw [withDensityᵥ_apply hf.neg hi]
    simp only [Pi.neg_apply]
  · rw [withDensityᵥ, withDensityᵥ, dif_neg hf, dif_neg, neg_zero]
    rwa [integrable_neg_iff]

/--
theorem `withDensityᵥ_neg'` / 定理 `withDensityᵥ_neg'`

English:
theorem withDensityᵥ_neg'
  statement: (μ.withDensityᵥ fun x => -f x) = -μ.withDensityᵥ f
  proof: withDensityᵥ_neg

@[simp]

中文:
定理 withDensityᵥ_neg'
  结论: (μ.withDensityᵥ fun x => -f x) = -μ.withDensityᵥ f
  证明: withDensityᵥ_neg

@[simp]
-/
theorem withDensityᵥ_neg' : (μ.withDensityᵥ fun x => -f x) = -μ.withDensityᵥ f :=
  withDensityᵥ_neg

@[simp]
/--
theorem `withDensityᵥ_add` / 定理 `withDensityᵥ_add`

English:
theorem withDensityᵥ_add
  given: (hf : Integrable f μ) (hg : Integrable g μ)
  proof: by
  ext1 i hi
  rw [withDensityᵥ_apply (hf.add hg) hi]; rw [_root_.add_apply]; rw [withDensityᵥ_apply hf hi]; rw [withDensityᵥ_apply hg hi]
  simp_rw [Pi.add_apply]
  rw [integral_add]
  · exact hf.integrableOn
  · exact hg.integrableOn

中文:
定理 withDensityᵥ_add
  条件: (hf : 可积 f μ) (hg : 可积 g μ)
  证明: by
  ext1 i hi
  rw [withDensityᵥ_apply (hf.add hg) hi]; rw [_root_.add_apply]; rw [withDensityᵥ_apply hf hi]; rw [withDensityᵥ_apply hg hi]
  simp_rw [Pi.add_apply]
  rw [integral_add]
  · exact hf.integrableOn
  · exact hg.integrableOn

Depends on / 依赖: Pi.add_apply, _root_, _root_.add_apply, add_apply, hf.add, hf.integrableOn, hg.integrableOn, integrableOn, integral_add, simp_rw
-/
theorem withDensityᵥ_add (hf : Integrable f μ) (hg : Integrable g μ) :
    μ.withDensityᵥ (f + g) = μ.withDensityᵥ f + μ.withDensityᵥ g := by
  ext1 i hi
  rw [withDensityᵥ_apply (hf.add hg) hi]; rw [_root_.add_apply]; rw [withDensityᵥ_apply hf hi]; rw [withDensityᵥ_apply hg hi]
  simp_rw [Pi.add_apply]
  rw [integral_add]
  · exact hf.integrableOn
  · exact hg.integrableOn

/--
theorem `withDensityᵥ_add'` / 定理 `withDensityᵥ_add'`

English:
theorem withDensityᵥ_add'
  given: (hf : Integrable f μ) (hg : Integrable g μ)
  proof: withDensityᵥ_add hf hg

@[simp]

中文:
定理 withDensityᵥ_add'
  条件: (hf : 可积 f μ) (hg : 可积 g μ)
  证明: withDensityᵥ_add hf hg

@[simp]
-/
theorem withDensityᵥ_add' (hf : Integrable f μ) (hg : Integrable g μ) :
    (μ.withDensityᵥ fun x => f x + g x) = μ.withDensityᵥ f + μ.withDensityᵥ g :=
  withDensityᵥ_add hf hg

@[simp]
/--
theorem `withDensityᵥ_sub` / 定理 `withDensityᵥ_sub`

English:
theorem withDensityᵥ_sub
  given: (hf : Integrable f μ) (hg : Integrable g μ)
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [withDensityᵥ_add hf hg.neg]; rw [withDensityᵥ_neg]

中文:
定理 withDensityᵥ_sub
  条件: (hf : 可积 f μ) (hg : 可积 g μ)
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [withDensityᵥ_add hf hg.neg]; rw [withDensityᵥ_neg]

Depends on / 依赖: hg.neg, sub_eq_add_neg
-/
theorem withDensityᵥ_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    μ.withDensityᵥ (f - g) = μ.withDensityᵥ f - μ.withDensityᵥ g := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [withDensityᵥ_add hf hg.neg]; rw [withDensityᵥ_neg]

/--
theorem `withDensityᵥ_sub'` / 定理 `withDensityᵥ_sub'`

English:
theorem withDensityᵥ_sub'
  given: (hf : Integrable f μ) (hg : Integrable g μ)
  proof: withDensityᵥ_sub hf hg

@[simp]

中文:
定理 withDensityᵥ_sub'
  条件: (hf : 可积 f μ) (hg : 可积 g μ)
  证明: withDensityᵥ_sub hf hg

@[simp]
-/
theorem withDensityᵥ_sub' (hf : Integrable f μ) (hg : Integrable g μ) :
    (μ.withDensityᵥ fun x => f x - g x) = μ.withDensityᵥ f - μ.withDensityᵥ g :=
  withDensityᵥ_sub hf hg

@[simp]
/--
theorem `withDensityᵥ_smul` / 定理 `withDensityᵥ_smul`

English:
theorem withDensityᵥ_smul
  statement: {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  proof: by
  by_cases hf : Integrable f μ
  · ext1 i hi
    rw [withDensityᵥ_apply (hf.smul r) hi]; rw [_root_.smul_apply]; rw [withDensityᵥ_apply hf hi]; rw [←
      integral_smul r f]
    simp only [Pi.smul_apply]
  · by_cases hr : r = 0
    · rw [hr, zero_smul, zero_smul, withDensityᵥ_zero]
    · rw [wit

中文:
定理 withDensityᵥ_smul
  结论: {𝕜 : 类型} [NontriviallyNormedField 𝕜] [赋范空间 𝕜 E]
  证明: by
  by_cases hf : Integrable f μ
  · ext1 i hi
    rw [withDensityᵥ_apply (hf.smul r) hi]; rw [_root_.smul_apply]; rw [withDensityᵥ_apply hf hi]; rw [←
      integral_smul r f]
    simp only [Pi.smul_apply]
  · by_cases hr : r = 0
    · rw [hr, zero_smul, zero_smul, withDensityᵥ_zero]
    · rw [wit

Depends on / 依赖: Integrable, Pi.smul_apply, _root_, _root_.smul_apply, dif_neg, hf.smul, integrable_smul_iff, integral_smul, smul_apply, smul_zero, zero_smul
-/
theorem withDensityᵥ_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass Real 𝕜 E] (f : α -> E) (r : 𝕜) : μ.withDensityᵥ (r • f) = r • μ.withDensityᵥ f := by
  by_cases hf : Integrable f μ
  · ext1 i hi
    rw [withDensityᵥ_apply (hf.smul r) hi]; rw [_root_.smul_apply]; rw [withDensityᵥ_apply hf hi]; rw [←
      integral_smul r f]
    simp only [Pi.smul_apply]
  · by_cases hr : r = 0
    · rw [hr, zero_smul, zero_smul, withDensityᵥ_zero]
    · rw [withDensityᵥ, withDensityᵥ, dif_neg hf, dif_neg, smul_zero]
      rwa [integrable_smul_iff hr f]

/--
theorem `withDensityᵥ_smul'` / 定理 `withDensityᵥ_smul'`

English:
theorem withDensityᵥ_smul'
  statement: {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  proof: withDensityᵥ_smul f r

中文:
定理 withDensityᵥ_smul'
  结论: {𝕜 : 类型} [NontriviallyNormedField 𝕜] [赋范空间 𝕜 E]
  证明: withDensityᵥ_smul f r
-/
theorem withDensityᵥ_smul' {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass Real 𝕜 E] (f : α -> E) (r : 𝕜) :
    (μ.withDensityᵥ fun x => r • f x) = r • μ.withDensityᵥ f :=
  withDensityᵥ_smul f r

/--
theorem `withDensityᵥ_smul_eq_withDensityᵥ_withDensity` / 定理 `withDensityᵥ_smul_eq_withDensityᵥ_withDensity`

English:
theorem withDensityᵥ_smul_eq_withDensityᵥ_withDensity
  statement: {f : α -> Real>=0} {g : α -> E}
  proof: by
  ext s hs
  rw [withDensityᵥ_apply hfg hs]; rw [withDensityᵥ_apply ((integrable_withDensity_iff_integrable_smul₀ hf).mpr hfg) hs]; rw [setIntegral_withDensity_eq_setIntegral_smul₀ hf.restrict _ hs]
  simp only [Pi.smul_apply']

中文:
定理 withDensityᵥ_smul_eq_withDensityᵥ_withDensity
  结论: {f : α -> 实数>=0} {g : α -> E}
  证明: by
  ext s hs
  rw [withDensityᵥ_apply hfg hs]; rw [withDensityᵥ_apply ((integrable_withDensity_iff_integrable_smul₀ hf).mpr hfg) hs]; rw [setIntegral_withDensity_eq_setIntegral_smul₀ hf.restrict _ hs]
  simp only [Pi.smul_apply']

Depends on / 依赖: Pi.smul_apply, hf.restrict, restrict, smul_apply
-/
theorem withDensityᵥ_smul_eq_withDensityᵥ_withDensity {f : α -> Real>=0} {g : α -> E}
    (hf : AEMeasurable f μ) (hfg : Integrable (f • g) μ) :
    μ.withDensityᵥ (f • g) = (μ.withDensity (fun x => f x)).withDensityᵥ g := by
  ext s hs
  rw [withDensityᵥ_apply hfg hs]; rw [withDensityᵥ_apply ((integrable_withDensity_iff_integrable_smul₀ hf).mpr hfg) hs]; rw [setIntegral_withDensity_eq_setIntegral_smul₀ hf.restrict _ hs]
  simp only [Pi.smul_apply']

/--
theorem `withDensityᵥ_smul_eq_withDensityᵥ_withDensity'` / 定理 `withDensityᵥ_smul_eq_withDensityᵥ_withDensity'`

English:
theorem withDensityᵥ_smul_eq_withDensityᵥ_withDensity'
  statement: {f : α -> Real>=0∞} {g : α -> E}
  proof: by
  rw [← withDensity_congr_ae (coe_toNNReal_ae_eq hflt)]; rw [← withDensityᵥ_smul_eq_withDensityᵥ_withDensity hf.ennreal_toNNReal hfg]
  apply congr_arg
  ext
  simp [NNReal.smul_def, ENNReal.coe_toNNReal_eq_toReal]

中文:
定理 withDensityᵥ_smul_eq_withDensityᵥ_withDensity'
  结论: {f : α -> 实数>=0∞} {g : α -> E}
  证明: by
  rw [← withDensity_congr_ae (coe_toNNReal_ae_eq hflt)]; rw [← withDensityᵥ_smul_eq_withDensityᵥ_withDensity hf.ennreal_toNNReal hfg]
  apply congr_arg
  ext
  simp [NNReal.smul_def, ENNReal.coe_toNNReal_eq_toReal]

Depends on / 依赖: ENNReal, ENNReal.coe_toNNReal_eq_toReal, NNReal, NNReal.smul_def, coe_toNNReal_ae_eq, coe_toNNReal_eq_toReal, congr_arg, ennreal_toNNReal, hf.ennreal_toNNReal, smul_def, withDensity_congr_ae
-/
theorem withDensityᵥ_smul_eq_withDensityᵥ_withDensity' {f : α -> Real>=0∞} {g : α -> E}
    (hf : AEMeasurable f μ) (hflt : forallᵐ x ∂μ, f x < ∞)
    (hfg : Integrable (fun x => (f x).toReal • g x) μ) :
    μ.withDensityᵥ (fun x => (f x).toReal • g x) = (μ.withDensity f).withDensityᵥ g := by
  rw [← withDensity_congr_ae (coe_toNNReal_ae_eq hflt)]; rw [← withDensityᵥ_smul_eq_withDensityᵥ_withDensity hf.ennreal_toNNReal hfg]
  apply congr_arg
  ext
  simp [NNReal.smul_def, ENNReal.coe_toNNReal_eq_toReal]

/--
theorem `Measure.withDensityᵥ_absolutelyContinuous` / 定理 `Measure.withDensityᵥ_absolutelyContinuous`

English:
theorem Measure.withDensityᵥ_absolutelyContinuous
  given: (μ : Measure α) (f : α -> Real)
  proof: by
  by_cases hf : Integrable f μ
  · refine VectorMeasure.AbsolutelyContinuous.mk fun i hi₁ hi₂ => ?_
    rw [toENNRealVectorMeasure_apply_measurable hi₁] at hi₂
    rw [withDensityᵥ_apply hf hi₁]; rw [Measure.restrict_zero_set hi₂]; rw [integral_zero_measure]
  · rw [withDensityᵥ, dif_neg hf]
    

中文:
定理 测度.withDensityᵥ_absolutelyContinuous
  条件: (μ : 测度 α) (f : α -> 实数)
  证明: by
  by_cases hf : Integrable f μ
  · refine VectorMeasure.AbsolutelyContinuous.mk fun i hi₁ hi₂ => ?_
    rw [toENNRealVectorMeasure_apply_measurable hi₁] at hi₂
    rw [withDensityᵥ_apply hf hi₁]; rw [Measure.restrict_zero_set hi₂]; rw [integral_zero_measure]
  · rw [withDensityᵥ, dif_neg hf]
    

Depends on / 依赖: AbsolutelyContinuous, Integrable, Measure, Measure.restrict_zero_set, VectorMeasure, VectorMeasure.AbsolutelyContinuous.mk, VectorMeasure.AbsolutelyContinuous.zero, dif_neg, integral_zero_measure, restrict_zero_set, toENNRealVectorMeasure_apply_measurable
-/
theorem Measure.withDensityᵥ_absolutelyContinuous (μ : Measure α) (f : α -> Real) :
    μ.withDensityᵥ f ≪ᵥ μ.toENNRealVectorMeasure := by
  by_cases hf : Integrable f μ
  · refine VectorMeasure.AbsolutelyContinuous.mk fun i hi₁ hi₂ => ?_
    rw [toENNRealVectorMeasure_apply_measurable hi₁] at hi₂
    rw [withDensityᵥ_apply hf hi₁]; rw [Measure.restrict_zero_set hi₂]; rw [integral_zero_measure]
  · rw [withDensityᵥ, dif_neg hf]
    exact VectorMeasure.AbsolutelyContinuous.zero _

/--
theorem `Integrable.ae_eq_of_withDensityᵥ_eq` / 定理 `Integrable.ae_eq_of_withDensityᵥ_eq`

English:
theorem Integrable.ae_eq_of_withDensityᵥ_eq
  statement: [CompleteSpace E] {f g : α -> E} (hf : Integrable f μ)
  proof: by
  refine hf.ae_eq_of_forall_setIntegral_eq f g hg fun i hi _ => ?_
  rw [← withDensityᵥ_apply hf hi]; rw [hfg]; rw [withDensityᵥ_apply hg hi]

中文:
定理 可积.ae_eq_of_withDensityᵥ_eq
  结论: [完备空间 E] {f g : α -> E} (hf : 可积 f μ)
  证明: by
  refine hf.ae_eq_of_forall_setIntegral_eq f g hg fun i hi _ => ?_
  rw [← withDensityᵥ_apply hf hi]; rw [hfg]; rw [withDensityᵥ_apply hg hi]

Depends on / 依赖: ae_eq_of_forall_setIntegral_eq, hf.ae_eq_of_forall_setIntegral_eq
-/
theorem Integrable.ae_eq_of_withDensityᵥ_eq [CompleteSpace E] {f g : α -> E} (hf : Integrable f μ)
    (hg : Integrable g μ) (hfg : μ.withDensityᵥ f = μ.withDensityᵥ g) : f =ᵐ[μ] g := by
  refine hf.ae_eq_of_forall_setIntegral_eq f g hg fun i hi _ => ?_
  rw [← withDensityᵥ_apply hf hi]; rw [hfg]; rw [withDensityᵥ_apply hg hi]

/--
theorem `WithDensityᵥEq.congr_ae` / 定理 `WithDensityᵥEq.congr_ae`

English:
theorem WithDensityᵥEq.congr_ae
  given: {f g : α -> E} (h : f =ᵐ[μ] g)
  proof: by
  by_cases hf : Integrable f μ
  · ext i hi
    rw [withDensityᵥ_apply hf hi]; rw [withDensityᵥ_apply (hf.congr h) hi]
    exact integral_congr_ae (ae_restrict_of_ae h)
  · have hg : ¬Integrable g μ := by intro hg; exact hf (hg.congr h.symm)
    rw [withDensityᵥ]; rw [withDensityᵥ]; rw [dif_neg h

中文:
定理 WithDensityᵥEq.congr_ae
  条件: {f g : α -> E} (h : f =ᵐ[μ] g)
  证明: by
  by_cases hf : Integrable f μ
  · ext i hi
    rw [withDensityᵥ_apply hf hi]; rw [withDensityᵥ_apply (hf.congr h) hi]
    exact integral_congr_ae (ae_restrict_of_ae h)
  · have hg : ¬Integrable g μ := by intro hg; exact hf (hg.congr h.symm)
    rw [withDensityᵥ]; rw [withDensityᵥ]; rw [dif_neg h

Depends on / 依赖: Integrable, ae_restrict_of_ae, dif_neg, h.symm, hf.congr, hg.congr, integral_congr_ae
-/
theorem WithDensityᵥEq.congr_ae {f g : α -> E} (h : f =ᵐ[μ] g) :
    μ.withDensityᵥ f = μ.withDensityᵥ g := by
  by_cases hf : Integrable f μ
  · ext i hi
    rw [withDensityᵥ_apply hf hi]; rw [withDensityᵥ_apply (hf.congr h) hi]
    exact integral_congr_ae (ae_restrict_of_ae h)
  · have hg : ¬Integrable g μ := by intro hg; exact hf (hg.congr h.symm)
    rw [withDensityᵥ]; rw [withDensityᵥ]; rw [dif_neg hf]; rw [dif_neg hg]

/--
theorem `Integrable.withDensityᵥ_eq_iff` / 定理 `Integrable.withDensityᵥ_eq_iff`

English:
theorem Integrable.withDensityᵥ_eq_iff
  statement: [CompleteSpace E]
  proof: ⟨fun hfg => hf.ae_eq_of_withDensityᵥ_eq hg hfg, fun h => WithDensityᵥEq.congr_ae h⟩

中文:
定理 可积.withDensityᵥ_eq_iff
  结论: [完备空间 E]
  证明: ⟨fun hfg => hf.ae_eq_of_withDensityᵥ_eq hg hfg, fun h => WithDensityᵥEq.congr_ae h⟩

Depends on / 依赖: Eq.congr_ae, congr_ae, hf.ae_eq_of_withDensity
-/
theorem Integrable.withDensityᵥ_eq_iff [CompleteSpace E]
    {f g : α -> E} (hf : Integrable f μ) (hg : Integrable g μ) :
    μ.withDensityᵥ f = μ.withDensityᵥ g ↔ f =ᵐ[μ] g :=
  ⟨fun hfg => hf.ae_eq_of_withDensityᵥ_eq hg hfg, fun h => WithDensityᵥEq.congr_ae h⟩

section SignedMeasure

/--
theorem `withDensityᵥ_toReal` / 定理 `withDensityᵥ_toReal`

English:
theorem withDensityᵥ_toReal
  given: {f : α -> Real>=0∞} (hfm : AEMeasurable f μ) (hf : (∫⁻ x, f x ∂μ) != ∞)
  proof: by
  have hfi := integrable_toReal_of_lintegral_ne_top hfm hf
  have := isFiniteMeasure_withDensity hf
  ext i hi
  rw [withDensityᵥ_apply hfi hi]; rw [toSignedMeasure_apply_measurable hi]; rw [measureReal_def]; rw [withDensity_apply _ hi]; rw [integral_toReal hfm.restrict]
  refine ae_lt_top' hfm.r

中文:
定理 withDensityᵥ_to实数
  条件: {f : α -> 实数>=0∞} (hfm : 几乎处处可测 f μ) (hf : (∫⁻ x, f x ∂μ) != ∞)
  证明: by
  have hfi := integrable_toReal_of_lintegral_ne_top hfm hf
  have := isFiniteMeasure_withDensity hf
  ext i hi
  rw [withDensityᵥ_apply hfi hi]; rw [toSignedMeasure_apply_measurable hi]; rw [measureReal_def]; rw [withDensity_apply _ hi]; rw [integral_toReal hfm.restrict]
  refine ae_lt_top' hfm.r

Depends on / 依赖: Set.subset_univ, ae_lt_top, conv_rhs, hfm.restrict, integrable_toReal_of_lintegral_ne_top, integral_toReal, isFiniteMeasure_withDensity, lintegral_mono_set, measureReal_def, ne_top_of_le_ne_top, restrict, setLIntegral_univ, subset_univ, toSignedMeasure_apply_measurable, withDensity_apply
-/
theorem withDensityᵥ_toReal {f : α -> Real>=0∞} (hfm : AEMeasurable f μ) (hf : (∫⁻ x, f x ∂μ) != ∞) :
    (μ.withDensityᵥ fun x => (f x).toReal) =
      @toSignedMeasure α _ (μ.withDensity f) (isFiniteMeasure_withDensity hf) := by
  have hfi := integrable_toReal_of_lintegral_ne_top hfm hf
  have := isFiniteMeasure_withDensity hf
  ext i hi
  rw [withDensityᵥ_apply hfi hi]; rw [toSignedMeasure_apply_measurable hi]; rw [measureReal_def]; rw [withDensity_apply _ hi]; rw [integral_toReal hfm.restrict]
  refine ae_lt_top' hfm.restrict (ne_top_of_le_ne_top hf ?_)
  conv_rhs => rw [← setLIntegral_univ]
  exact lintegral_mono_set (Set.subset_univ _)

/--
theorem `withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part` / 定理 `withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part`

English:
theorem withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part
  statement: {f : α -> Real}
  proof: by
  have := isFiniteMeasure_withDensity_ofReal hfi.2
  have := isFiniteMeasure_withDensity_ofReal hfi.neg.2
  ext i hi
  rw [withDensityᵥ_apply hfi hi]; rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi.integrableOn]; rw [_root_.sub_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [

中文:
定理 withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part
  结论: {f : α -> 实数}
  证明: by
  have := isFiniteMeasure_withDensity_ofReal hfi.2
  have := isFiniteMeasure_withDensity_ofReal hfi.neg.2
  ext i hi
  rw [withDensityᵥ_apply hfi hi]; rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi.integrableOn]; rw [_root_.sub_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [

Depends on / 依赖: _root_, _root_.sub_apply, hfi.integrableOn, hfi.neg, integrableOn, integral_eq_lintegral_pos_part_sub_lintegral_neg_part, isFiniteMeasure_withDensity_ofReal, measureReal_def, sub_apply, toSignedMeasure_apply_measurable, withDensity_apply
-/
theorem withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part {f : α -> Real}
    (hfi : Integrable f μ) :
    μ.withDensityᵥ f =
      @toSignedMeasure α _ (μ.withDensity fun x => ENNReal.ofReal <| f x)
          (isFiniteMeasure_withDensity_ofReal hfi.2) -
        @toSignedMeasure α _ (μ.withDensity fun x => ENNReal.ofReal <| -f x)
          (isFiniteMeasure_withDensity_ofReal hfi.neg.2) := by
  have := isFiniteMeasure_withDensity_ofReal hfi.2
  have := isFiniteMeasure_withDensity_ofReal hfi.neg.2
  ext i hi
  rw [withDensityᵥ_apply hfi hi]; rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi.integrableOn]; rw [_root_.sub_apply]; rw [toSignedMeasure_apply_measurable hi]; rw [toSignedMeasure_apply_measurable hi]; rw [measureReal_def]; rw [measureReal_def]; rw [withDensity_apply _ hi]; rw [withDensity_apply _ hi]

/--
theorem `Integrable.withDensityᵥ_trim_eq_integral` / 定理 `Integrable.withDensityᵥ_trim_eq_integral`

English:
theorem Integrable.withDensityᵥ_trim_eq_integral
  statement: {m m0 : MeasurableSpace α} {μ : Measure α}
  proof: by
  rw [VectorMeasure.trim_measurableSet_eq hm hi]; rw [withDensityᵥ_apply hf (hm _ hi)]

中文:
定理 可积.withDensityᵥ_trim_eq_integral
  结论: {m m0 : 可测空间 α} {μ : 测度 α}
  证明: by
  rw [VectorMeasure.trim_measurableSet_eq hm hi]; rw [withDensityᵥ_apply hf (hm _ hi)]

Depends on / 依赖: VectorMeasure, VectorMeasure.trim_measurableSet_eq, trim_measurableSet_eq
-/
theorem Integrable.withDensityᵥ_trim_eq_integral {m m0 : MeasurableSpace α} {μ : Measure α}
    (hm : m <= m0) {f : α -> Real} (hf : Integrable f μ) {i : Set α} (hi : MeasurableSet[m] i) :
    (μ.withDensityᵥ f).trim hm i = ∫ x in i, f x ∂μ := by
  rw [VectorMeasure.trim_measurableSet_eq hm hi]; rw [withDensityᵥ_apply hf (hm _ hi)]

/--
theorem `Integrable.withDensityᵥ_trim_absolutelyContinuous` / 定理 `Integrable.withDensityᵥ_trim_absolutelyContinuous`

English:
theorem Integrable.withDensityᵥ_trim_absolutelyContinuous
  statement: {m m0 : MeasurableSpace α} {μ : Measure α}
  proof: by
  refine VectorMeasure.AbsolutelyContinuous.mk fun j hj₁ hj₂ => ?_
  rw [Measure.toENNRealVectorMeasure_apply_measurable hj₁]; rw [trim_measurableSet_eq hm hj₁] at hj₂
  rw [VectorMeasure.trim_measurableSet_eq hm hj₁]; rw [withDensityᵥ_apply hfi (hm _ hj₁)]
  simp only [Measure.restrict_eq_zero.m

中文:
定理 可积.withDensityᵥ_trim_absolutelyContinuous
  结论: {m m0 : 可测空间 α} {μ : 测度 α}
  证明: by
  refine VectorMeasure.AbsolutelyContinuous.mk fun j hj₁ hj₂ => ?_
  rw [Measure.toENNRealVectorMeasure_apply_measurable hj₁]; rw [trim_measurableSet_eq hm hj₁] at hj₂
  rw [VectorMeasure.trim_measurableSet_eq hm hj₁]; rw [withDensityᵥ_apply hfi (hm _ hj₁)]
  simp only [Measure.restrict_eq_zero.m

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.restrict_eq_zero.mpr, Measure.toENNRealVectorMeasure_apply_measurable, VectorMeasure, VectorMeasure.AbsolutelyContinuous.mk, VectorMeasure.trim_measurableSet_eq, integral_zero_measure, restrict_eq_zero, toENNRealVectorMeasure_apply_measurable, trim_measurableSet_eq
-/
theorem Integrable.withDensityᵥ_trim_absolutelyContinuous {m m0 : MeasurableSpace α} {μ : Measure α}
    (hm : m <= m0) (hfi : Integrable f μ) :
    (μ.withDensityᵥ f).trim hm ≪ᵥ (μ.trim hm).toENNRealVectorMeasure := by
  refine VectorMeasure.AbsolutelyContinuous.mk fun j hj₁ hj₂ => ?_
  rw [Measure.toENNRealVectorMeasure_apply_measurable hj₁]; rw [trim_measurableSet_eq hm hj₁] at hj₂
  rw [VectorMeasure.trim_measurableSet_eq hm hj₁]; rw [withDensityᵥ_apply hfi (hm _ hj₁)]
  simp only [Measure.restrict_eq_zero.mpr hj₂, integral_zero_measure]

end SignedMeasure

end MeasureTheory
