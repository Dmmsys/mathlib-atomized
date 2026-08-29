/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Lebesgue and Bochner integrals of conditional kernels

Integrals of `ProbabilityTheory.Kernel.condKernel` and `MeasureTheory.Measure.condKernel`.

## Main statements

* `ProbabilityTheory.setIntegral_condKernel`: the integral
  `∫ b in s, ∫ ω in t, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a)` is equal to
  `∫ x in s ×ˢ t, f x ∂(κ a)`.
* `MeasureTheory.Measure.setIntegral_condKernel`:
  `∫ b in s, ∫ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in s ×ˢ t, f x ∂ρ`

Corresponding statements for the Lebesgue integral and/or without the sets `s` and `t` are also
provided.
-/

public section

open MeasureTheory ProbabilityTheory MeasurableSpace

open scoped ENNReal

namespace ProbabilityTheory

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

section Lintegral

variable [CountableOrCountablyGenerated α β] {κ : Kernel α (β × Ω)} [IsFiniteKernel κ]
  {f : β × Ω -> Real>=0∞}

/--
lemma `lintegral_condKernel_mem` / 引理 `lintegral_condKernel_mem`

English:
lemma lintegral_condKernel_mem
  given: (a : α) {s : Set (β × Ω)} (hs : MeasurableSet s)
  proof: by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  simp_rw [Kernel.compProd_apply hs]

中文:
引理 lintegral_condKernel_mem
  条件: (a : α) {s : 集合 (β × Ω)} (hs : 可测集 s)
  证明: by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  simp_rw [Kernel.compProd_apply hs]

Depends on / 依赖: Kernel, Kernel.compProd_apply, compProd_apply, condKernel, conv_rhs, disintegrate, simp_rw
-/
lemma lintegral_condKernel_mem (a : α) {s : Set (β × Ω)} (hs : MeasurableSet s) :
    ∫⁻ x, Kernel.condKernel κ (a, x) (Prod.mk x ⁻¹' s) ∂(Kernel.fst κ a) = κ a s := by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  simp_rw [Kernel.compProd_apply hs]

/--
lemma `setLIntegral_condKernel_eq_measure_prod` / 引理 `setLIntegral_condKernel_eq_measure_prod`

English:
lemma setLIntegral_condKernel_eq_measure_prod
  statement: (a : α) {s : Set β} (hs : MeasurableSet s)
  proof: by
  have : κ a (s ×ˢ t) = (Kernel.fst κ otimesₖ Kernel.condKernel κ) a (s ×ˢ t) := by
    congr; exact (κ.disintegrate _).symm
  simpa [this] using (Kernel.compProd_apply_prod hs ht).symm

中文:
引理 setL整数egral_condKernel_eq_measure_prod
  结论: (a : α) {s : 集合 β} (hs : 可测集 s)
  证明: by
  have : κ a (s ×ˢ t) = (Kernel.fst κ otimesₖ Kernel.condKernel κ) a (s ×ˢ t) := by
    congr; exact (κ.disintegrate _).symm
  simpa [this] using (Kernel.compProd_apply_prod hs ht).symm

Depends on / 依赖: Kernel, Kernel.compProd_apply_prod, Kernel.condKernel, Kernel.fst, compProd_apply_prod, condKernel, disintegrate
-/
lemma setLIntegral_condKernel_eq_measure_prod (a : α) {s : Set β} (hs : MeasurableSet s)
    {t : Set Ω} (ht : MeasurableSet t) :
    ∫⁻ b in s, Kernel.condKernel κ (a, b) t ∂(Kernel.fst κ a) = κ a (s ×ˢ t) := by
  have : κ a (s ×ˢ t) = (Kernel.fst κ otimesₖ Kernel.condKernel κ) a (s ×ˢ t) := by
    congr; exact (κ.disintegrate _).symm
  simpa [this] using (Kernel.compProd_apply_prod hs ht).symm

/--
lemma `lintegral_condKernel` / 引理 `lintegral_condKernel`

English:
lemma lintegral_condKernel
  given: (hf : Measurable f) (a : α)
  proof: by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [Kernel.lintegral_compProd _ _ _ hf]

中文:
引理 lintegral_condKernel
  条件: (hf : 可测 f) (a : α)
  证明: by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [Kernel.lintegral_compProd _ _ _ hf]

Depends on / 依赖: Kernel, Kernel.lintegral_compProd, condKernel, conv_rhs, disintegrate, lintegral_compProd
-/
lemma lintegral_condKernel (hf : Measurable f) (a : α) :
    ∫⁻ b, ∫⁻ ω, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a) = ∫⁻ x, f x ∂(κ a) := by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [Kernel.lintegral_compProd _ _ _ hf]

/--
lemma `setLIntegral_condKernel` / 引理 `setLIntegral_condKernel`

English:
lemma setLIntegral_condKernel
  statement: (hf : Measurable f) (a : α) {s : Set β}
  proof: by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [Kernel.setLIntegral_compProd _ _ _ hf hs ht]

中文:
引理 setL整数egral_condKernel
  结论: (hf : 可测 f) (a : α) {s : 集合 β}
  证明: by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [Kernel.setLIntegral_compProd _ _ _ hf hs ht]

Depends on / 依赖: Kernel, Kernel.setLIntegral_compProd, condKernel, conv_rhs, disintegrate, setLIntegral_compProd
-/
lemma setLIntegral_condKernel (hf : Measurable f) (a : α) {s : Set β}
    (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t) :
    ∫⁻ b in s, ∫⁻ ω in t, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a)
      = ∫⁻ x in s ×ˢ t, f x ∂(κ a) := by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [Kernel.setLIntegral_compProd _ _ _ hf hs ht]

/--
lemma `setLIntegral_condKernel_univ_right` / 引理 `setLIntegral_condKernel_univ_right`

English:
lemma setLIntegral_condKernel_univ_right
  statement: (hf : Measurable f) (a : α) {s : Set β}
  proof: by
  rw [← setLIntegral_condKernel hf a hs MeasurableSet.univ]; simp_rw [Measure.restrict_univ]

中文:
引理 setL整数egral_condKernel_univ_right
  结论: (hf : 可测 f) (a : α) {s : 集合 β}
  证明: by
  rw [← setLIntegral_condKernel hf a hs MeasurableSet.univ]; simp_rw [Measure.restrict_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_univ, restrict_univ, setLIntegral_condKernel, simp_rw
-/
lemma setLIntegral_condKernel_univ_right (hf : Measurable f) (a : α) {s : Set β}
    (hs : MeasurableSet s) :
    ∫⁻ b in s, ∫⁻ ω, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a)
      = ∫⁻ x in s ×ˢ Set.univ, f x ∂(κ a) := by
  rw [← setLIntegral_condKernel hf a hs MeasurableSet.univ]; simp_rw [Measure.restrict_univ]

/--
lemma `setLIntegral_condKernel_univ_left` / 引理 `setLIntegral_condKernel_univ_left`

English:
lemma setLIntegral_condKernel_univ_left
  statement: (hf : Measurable f) (a : α) {t : Set Ω}
  proof: by
  rw [← setLIntegral_condKernel hf a MeasurableSet.univ ht]; simp_rw [Measure.restrict_univ]

中文:
引理 setL整数egral_condKernel_univ_left
  结论: (hf : 可测 f) (a : α) {t : 集合 Ω}
  证明: by
  rw [← setLIntegral_condKernel hf a MeasurableSet.univ ht]; simp_rw [Measure.restrict_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_univ, restrict_univ, setLIntegral_condKernel, simp_rw
-/
lemma setLIntegral_condKernel_univ_left (hf : Measurable f) (a : α) {t : Set Ω}
    (ht : MeasurableSet t) :
    ∫⁻ b, ∫⁻ ω in t, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a)
      = ∫⁻ x in Set.univ ×ˢ t, f x ∂(κ a) := by
  rw [← setLIntegral_condKernel hf a MeasurableSet.univ ht]; simp_rw [Measure.restrict_univ]

end Lintegral

section Integral

variable [CountableOrCountablyGenerated α β] {κ : Kernel α (β × Ω)} [IsFiniteKernel κ]
  {E : Type*} {f : β × Ω -> E} [NormedAddCommGroup E] [NormedSpace Real E]

/--
lemma `_root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_condKernel` / 引理 `_root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_condKernel`

English:
lemma _root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_condKernel
  statement: (a : α)
  proof: by
  rw [← κ.disintegrate κ.condKernel] at hf
  exact AEStronglyMeasurable.integral_kernel_compProd hf

中文:
引理 _root_.测度论.AEStronglyMeasurable.integral_kernel_condKernel
  结论: (a : α)
  证明: by
  rw [← κ.disintegrate κ.condKernel] at hf
  exact AEStronglyMeasurable.integral_kernel_compProd hf

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.integral_kernel_compProd, condKernel, disintegrate, integral_kernel_compProd
-/
lemma _root_.MeasureTheory.AEStronglyMeasurable.integral_kernel_condKernel (a : α)
    (hf : AEStronglyMeasurable f (κ a)) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂(Kernel.condKernel κ (a, x)))
      (Kernel.fst κ a) := by
  rw [← κ.disintegrate κ.condKernel] at hf
  exact AEStronglyMeasurable.integral_kernel_compProd hf

/--
lemma `integral_condKernel` / 引理 `integral_condKernel`

English:
lemma integral_condKernel
  given: (a : α) (hf : Integrable f (κ a))
  proof: by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [← κ.disintegrate κ.condKernel] at hf
  rw [integral_compProd hf]

中文:
引理 integral_condKernel
  条件: (a : α) (hf : 可积 f (κ a))
  证明: by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [← κ.disintegrate κ.condKernel] at hf
  rw [integral_compProd hf]

Depends on / 依赖: condKernel, conv_rhs, disintegrate, integral_compProd
-/
lemma integral_condKernel (a : α) (hf : Integrable f (κ a)) :
    ∫ b, ∫ ω, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a) = ∫ x, f x ∂(κ a) := by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [← κ.disintegrate κ.condKernel] at hf
  rw [integral_compProd hf]

/--
lemma `setIntegral_condKernel` / 引理 `setIntegral_condKernel`

English:
lemma setIntegral_condKernel
  statement: (a : α) {s : Set β} (hs : MeasurableSet s)
  proof: by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [← κ.disintegrate κ.condKernel] at hf
  rw [setIntegral_compProd hs ht hf]

中文:
引理 set整数egral_condKernel
  结论: (a : α) {s : 集合 β} (hs : 可测集 s)
  证明: by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [← κ.disintegrate κ.condKernel] at hf
  rw [setIntegral_compProd hs ht hf]

Depends on / 依赖: condKernel, conv_rhs, disintegrate, setIntegral_compProd
-/
lemma setIntegral_condKernel (a : α) {s : Set β} (hs : MeasurableSet s)
    {t : Set Ω} (ht : MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) (κ a)) :
    ∫ b in s, ∫ ω in t, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a)
      = ∫ x in s ×ˢ t, f x ∂(κ a) := by
  conv_rhs => rw [← κ.disintegrate κ.condKernel]
  rw [← κ.disintegrate κ.condKernel] at hf
  rw [setIntegral_compProd hs ht hf]

/--
lemma `setIntegral_condKernel_univ_right` / 引理 `setIntegral_condKernel_univ_right`

English:
lemma setIntegral_condKernel_univ_right
  statement: (a : α) {s : Set β} (hs : MeasurableSet s)
  proof: by
  rw [← setIntegral_condKernel a hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]

中文:
引理 set整数egral_condKernel_univ_right
  结论: (a : α) {s : 集合 β} (hs : 可测集 s)
  证明: by
  rw [← setIntegral_condKernel a hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_univ, restrict_univ, setIntegral_condKernel, simp_rw
-/
lemma setIntegral_condKernel_univ_right (a : α) {s : Set β} (hs : MeasurableSet s)
    (hf : IntegrableOn f (s ×ˢ Set.univ) (κ a)) :
    ∫ b in s, ∫ ω, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a)
      = ∫ x in s ×ˢ Set.univ, f x ∂(κ a) := by
  rw [← setIntegral_condKernel a hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]

/--
lemma `setIntegral_condKernel_univ_left` / 引理 `setIntegral_condKernel_univ_left`

English:
lemma setIntegral_condKernel_univ_left
  statement: (a : α) {t : Set Ω} (ht : MeasurableSet t)
  proof: by
  rw [← setIntegral_condKernel a MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]

中文:
引理 set整数egral_condKernel_univ_left
  结论: (a : α) {t : 集合 Ω} (ht : 可测集 t)
  证明: by
  rw [← setIntegral_condKernel a MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_univ, restrict_univ, setIntegral_condKernel, simp_rw
-/
lemma setIntegral_condKernel_univ_left (a : α) {t : Set Ω} (ht : MeasurableSet t)
    (hf : IntegrableOn f (Set.univ ×ˢ t) (κ a)) :
    ∫ b, ∫ ω in t, f (b, ω) ∂(Kernel.condKernel κ (a, b)) ∂(Kernel.fst κ a)
      = ∫ x in Set.univ ×ˢ t, f x ∂(κ a) := by
  rw [← setIntegral_condKernel a MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]

end Integral

end ProbabilityTheory

namespace MeasureTheory.Measure

variable {β Ω : Type*} {mβ : MeasurableSpace β}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

section Lintegral

variable {ρ : Measure (β × Ω)} [IsFiniteMeasure ρ]
  {f : β × Ω -> Real>=0∞}

/--
lemma `lintegral_condKernel_mem` / 引理 `lintegral_condKernel_mem`

English:
lemma lintegral_condKernel_mem
  given: {s : Set (β × Ω)} (hs : MeasurableSet s)
  proof: by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  simp_rw [compProd_apply hs]
  rfl

中文:
引理 lintegral_condKernel_mem
  条件: {s : 集合 (β × Ω)} (hs : 可测集 s)
  证明: by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  simp_rw [compProd_apply hs]
  rfl

Depends on / 依赖: compProd_apply, condKernel, conv_rhs, disintegrate, simp_rw
-/
lemma lintegral_condKernel_mem {s : Set (β × Ω)} (hs : MeasurableSet s) :
    ∫⁻ x, ρ.condKernel x {y | (x, y) in s} ∂ρ.fst = ρ s := by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  simp_rw [compProd_apply hs]
  rfl

/--
lemma `setLIntegral_condKernel_eq_measure_prod` / 引理 `setLIntegral_condKernel_eq_measure_prod`

English:
lemma setLIntegral_condKernel_eq_measure_prod
  statement: {s : Set β} (hs : MeasurableSet s) {t : Set Ω}
  proof: by
  have : ρ (s ×ˢ t) = (ρ.fst otimesₘ ρ.condKernel) (s ×ˢ t) := by
    congr; exact (ρ.disintegrate _).symm
  simpa [this] using (compProd_apply_prod hs ht).symm

中文:
引理 setL整数egral_condKernel_eq_measure_prod
  结论: {s : 集合 β} (hs : 可测集 s) {t : 集合 Ω}
  证明: by
  have : ρ (s ×ˢ t) = (ρ.fst otimesₘ ρ.condKernel) (s ×ˢ t) := by
    congr; exact (ρ.disintegrate _).symm
  simpa [this] using (compProd_apply_prod hs ht).symm

Depends on / 依赖: compProd_apply_prod, condKernel, disintegrate
-/
lemma setLIntegral_condKernel_eq_measure_prod {s : Set β} (hs : MeasurableSet s) {t : Set Ω}
    (ht : MeasurableSet t) :
    ∫⁻ b in s, ρ.condKernel b t ∂ρ.fst = ρ (s ×ˢ t) := by
  have : ρ (s ×ˢ t) = (ρ.fst otimesₘ ρ.condKernel) (s ×ˢ t) := by
    congr; exact (ρ.disintegrate _).symm
  simpa [this] using (compProd_apply_prod hs ht).symm

/--
lemma `lintegral_condKernel` / 引理 `lintegral_condKernel`

English:
lemma lintegral_condKernel
  given: (hf : Measurable f)
  proof: by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [lintegral_compProd hf]

中文:
引理 lintegral_condKernel
  条件: (hf : 可测 f)
  证明: by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [lintegral_compProd hf]

Depends on / 依赖: condKernel, conv_rhs, disintegrate, lintegral_compProd
-/
lemma lintegral_condKernel (hf : Measurable f) :
    ∫⁻ b, ∫⁻ ω, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫⁻ x, f x ∂ρ := by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [lintegral_compProd hf]

/--
lemma `setLIntegral_condKernel` / 引理 `setLIntegral_condKernel`

English:
lemma setLIntegral_condKernel
  statement: (hf : Measurable f) {s : Set β}
  proof: by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [setLIntegral_compProd hf hs ht]

中文:
引理 setL整数egral_condKernel
  结论: (hf : 可测 f) {s : 集合 β}
  证明: by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [setLIntegral_compProd hf hs ht]

Depends on / 依赖: condKernel, conv_rhs, disintegrate, setLIntegral_compProd
-/
lemma setLIntegral_condKernel (hf : Measurable f) {s : Set β}
    (hs : MeasurableSet s) {t : Set Ω} (ht : MeasurableSet t) :
    ∫⁻ b in s, ∫⁻ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst
      = ∫⁻ x in s ×ˢ t, f x ∂ρ := by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [setLIntegral_compProd hf hs ht]

/--
lemma `setLIntegral_condKernel_univ_right` / 引理 `setLIntegral_condKernel_univ_right`

English:
lemma setLIntegral_condKernel_univ_right
  statement: (hf : Measurable f) {s : Set β}
  proof: by
  rw [← setLIntegral_condKernel hf hs MeasurableSet.univ]; simp_rw [Measure.restrict_univ]

中文:
引理 setL整数egral_condKernel_univ_right
  结论: (hf : 可测 f) {s : 集合 β}
  证明: by
  rw [← setLIntegral_condKernel hf hs MeasurableSet.univ]; simp_rw [Measure.restrict_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_univ, restrict_univ, setLIntegral_condKernel, simp_rw
-/
lemma setLIntegral_condKernel_univ_right (hf : Measurable f) {s : Set β}
    (hs : MeasurableSet s) :
    ∫⁻ b in s, ∫⁻ ω, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst
      = ∫⁻ x in s ×ˢ Set.univ, f x ∂ρ := by
  rw [← setLIntegral_condKernel hf hs MeasurableSet.univ]; simp_rw [Measure.restrict_univ]

/--
lemma `setLIntegral_condKernel_univ_left` / 引理 `setLIntegral_condKernel_univ_left`

English:
lemma setLIntegral_condKernel_univ_left
  statement: (hf : Measurable f) {t : Set Ω}
  proof: by
  rw [← setLIntegral_condKernel hf MeasurableSet.univ ht]; simp_rw [Measure.restrict_univ]

中文:
引理 setL整数egral_condKernel_univ_left
  结论: (hf : 可测 f) {t : 集合 Ω}
  证明: by
  rw [← setLIntegral_condKernel hf MeasurableSet.univ ht]; simp_rw [Measure.restrict_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_univ, restrict_univ, setLIntegral_condKernel, simp_rw
-/
lemma setLIntegral_condKernel_univ_left (hf : Measurable f) {t : Set Ω}
    (ht : MeasurableSet t) :
    ∫⁻ b, ∫⁻ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst
      = ∫⁻ x in Set.univ ×ˢ t, f x ∂ρ := by
  rw [← setLIntegral_condKernel hf MeasurableSet.univ ht]; simp_rw [Measure.restrict_univ]

end Lintegral

section Integral

variable {ρ : Measure (β × Ω)} [IsFiniteMeasure ρ]
  {E : Type*} {f : β × Ω -> E} [NormedAddCommGroup E] [NormedSpace Real E]

/--
lemma `_root_.MeasureTheory.AEStronglyMeasurable.integral_condKernel` / 引理 `_root_.MeasureTheory.AEStronglyMeasurable.integral_condKernel`

English:
lemma _root_.MeasureTheory.AEStronglyMeasurable.integral_condKernel
  proof: by
  rw [← ρ.disintegrate ρ.condKernel] at hf
  exact AEStronglyMeasurable.integral_kernel_compProd hf

中文:
引理 _root_.测度论.AEStronglyMeasurable.integral_condKernel
  证明: by
  rw [← ρ.disintegrate ρ.condKernel] at hf
  exact AEStronglyMeasurable.integral_kernel_compProd hf

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.integral_kernel_compProd, condKernel, disintegrate, integral_kernel_compProd
-/
lemma _root_.MeasureTheory.AEStronglyMeasurable.integral_condKernel
    (hf : AEStronglyMeasurable f ρ) :
    AEStronglyMeasurable (fun x => ∫ y, f (x, y) ∂ρ.condKernel x) ρ.fst := by
  rw [← ρ.disintegrate ρ.condKernel] at hf
  exact AEStronglyMeasurable.integral_kernel_compProd hf

/--
lemma `integral_condKernel` / 引理 `integral_condKernel`

English:
lemma integral_condKernel
  given: (hf : Integrable f ρ)
  proof: by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [← ρ.disintegrate ρ.condKernel] at hf
  rw [integral_compProd hf]

中文:
引理 integral_condKernel
  条件: (hf : 可积 f ρ)
  证明: by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [← ρ.disintegrate ρ.condKernel] at hf
  rw [integral_compProd hf]

Depends on / 依赖: condKernel, conv_rhs, disintegrate, integral_compProd
-/
lemma integral_condKernel (hf : Integrable f ρ) :
    ∫ b, ∫ ω, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x, f x ∂ρ := by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [← ρ.disintegrate ρ.condKernel] at hf
  rw [integral_compProd hf]

/--
lemma `setIntegral_condKernel` / 引理 `setIntegral_condKernel`

English:
lemma setIntegral_condKernel
  statement: {s : Set β} (hs : MeasurableSet s)
  proof: by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [← ρ.disintegrate ρ.condKernel] at hf
  rw [setIntegral_compProd hs ht hf]

中文:
引理 set整数egral_condKernel
  结论: {s : 集合 β} (hs : 可测集 s)
  证明: by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [← ρ.disintegrate ρ.condKernel] at hf
  rw [setIntegral_compProd hs ht hf]

Depends on / 依赖: condKernel, conv_rhs, disintegrate, setIntegral_compProd
-/
lemma setIntegral_condKernel {s : Set β} (hs : MeasurableSet s)
    {t : Set Ω} (ht : MeasurableSet t) (hf : IntegrableOn f (s ×ˢ t) ρ) :
    ∫ b in s, ∫ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in s ×ˢ t, f x ∂ρ := by
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [← ρ.disintegrate ρ.condKernel] at hf
  rw [setIntegral_compProd hs ht hf]

/--
lemma `setIntegral_condKernel_univ_right` / 引理 `setIntegral_condKernel_univ_right`

English:
lemma setIntegral_condKernel_univ_right
  statement: {s : Set β} (hs : MeasurableSet s)
  proof: by
  rw [← setIntegral_condKernel hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]

中文:
引理 set整数egral_condKernel_univ_right
  结论: {s : 集合 β} (hs : 可测集 s)
  证明: by
  rw [← setIntegral_condKernel hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_univ, restrict_univ, setIntegral_condKernel, simp_rw
-/
lemma setIntegral_condKernel_univ_right {s : Set β} (hs : MeasurableSet s)
    (hf : IntegrableOn f (s ×ˢ Set.univ) ρ) :
    ∫ b in s, ∫ ω, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in s ×ˢ Set.univ, f x ∂ρ := by
  rw [← setIntegral_condKernel hs MeasurableSet.univ hf]; simp_rw [Measure.restrict_univ]

/--
lemma `setIntegral_condKernel_univ_left` / 引理 `setIntegral_condKernel_univ_left`

English:
lemma setIntegral_condKernel_univ_left
  statement: {t : Set Ω} (ht : MeasurableSet t)
  proof: by
  rw [← setIntegral_condKernel MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]

中文:
引理 set整数egral_condKernel_univ_left
  结论: {t : 集合 Ω} (ht : 可测集 t)
  证明: by
  rw [← setIntegral_condKernel MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, Measure, Measure.restrict_univ, restrict_univ, setIntegral_condKernel, simp_rw
-/
lemma setIntegral_condKernel_univ_left {t : Set Ω} (ht : MeasurableSet t)
    (hf : IntegrableOn f (Set.univ ×ˢ t) ρ) :
    ∫ b, ∫ ω in t, f (b, ω) ∂(ρ.condKernel b) ∂ρ.fst = ∫ x in Set.univ ×ˢ t, f x ∂ρ := by
  rw [← setIntegral_condKernel MeasurableSet.univ ht hf]; simp_rw [Measure.restrict_univ]

end Integral

end MeasureTheory.Measure

namespace MeasureTheory

/-! ### Integrability

We place these lemmas in the `MeasureTheory` namespace to enable dot notation. -/

open ProbabilityTheory

variable {α Ω E F : Type*} {mα : MeasurableSpace α} [MeasurableSpace Ω]
  [StandardBorelSpace Ω] [Nonempty Ω] [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]

/--
theorem `AEStronglyMeasurable.ae_integrable_condKernel_iff` / 定理 `AEStronglyMeasurable.ae_integrable_condKernel_iff`

English:
theorem AEStronglyMeasurable.ae_integrable_condKernel_iff
  statement: {f : α × Ω -> F}
  proof: by
  rw [← ρ.disintegrate ρ.condKernel] at hf
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [Measure.integrable_compProd_iff hf]

中文:
定理 AEStronglyMeasurable.ae_integrable_condKernel_iff
  结论: {f : α × Ω -> F}
  证明: by
  rw [← ρ.disintegrate ρ.condKernel] at hf
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [Measure.integrable_compProd_iff hf]

Depends on / 依赖: Measure, Measure.integrable_compProd_iff, condKernel, conv_rhs, disintegrate, integrable_compProd_iff
-/
theorem AEStronglyMeasurable.ae_integrable_condKernel_iff {f : α × Ω -> F}
    (hf : AEStronglyMeasurable f ρ) :
    (forallᵐ a ∂ρ.fst, Integrable (fun ω => f (a, ω)) (ρ.condKernel a)) ∧
      Integrable (fun a => ∫ ω, ‖f (a, ω)‖ ∂ρ.condKernel a) ρ.fst ↔ Integrable f ρ := by
  rw [← ρ.disintegrate ρ.condKernel] at hf
  conv_rhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [Measure.integrable_compProd_iff hf]

/--
theorem `Integrable.condKernel_ae` / 定理 `Integrable.condKernel_ae`

English:
theorem Integrable.condKernel_ae
  given: {f : α × Ω -> F} (hf_int : Integrable f ρ)
  proof: by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  rw [← hf_ae.ae_integrable_condKernel_iff] at hf_int
  exact hf_int.1

中文:
定理 可积.condKernel_ae
  条件: {f : α × Ω -> F} (hf_int : 可积 f ρ)
  证明: by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  rw [← hf_ae.ae_integrable_condKernel_iff] at hf_int
  exact hf_int.1

Depends on / 依赖: AEStronglyMeasurable, ae_integrable_condKernel_iff, hf_ae, hf_ae.ae_integrable_condKernel_iff, hf_int
-/
theorem Integrable.condKernel_ae {f : α × Ω -> F} (hf_int : Integrable f ρ) :
    forallᵐ a ∂ρ.fst, Integrable (fun ω => f (a, ω)) (ρ.condKernel a) := by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  rw [← hf_ae.ae_integrable_condKernel_iff] at hf_int
  exact hf_int.1

/--
theorem `Integrable.integral_norm_condKernel` / 定理 `Integrable.integral_norm_condKernel`

English:
theorem Integrable.integral_norm_condKernel
  given: {f : α × Ω -> F} (hf_int : Integrable f ρ)
  proof: by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  rw [← hf_ae.ae_integrable_condKernel_iff] at hf_int
  exact hf_int.2

中文:
定理 可积.integral_norm_condKernel
  条件: {f : α × Ω -> F} (hf_int : 可积 f ρ)
  证明: by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  rw [← hf_ae.ae_integrable_condKernel_iff] at hf_int
  exact hf_int.2

Depends on / 依赖: AEStronglyMeasurable, ae_integrable_condKernel_iff, hf_ae, hf_ae.ae_integrable_condKernel_iff, hf_int
-/
theorem Integrable.integral_norm_condKernel {f : α × Ω -> F} (hf_int : Integrable f ρ) :
    Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂ρ.condKernel x) ρ.fst := by
  have hf_ae : AEStronglyMeasurable f ρ := hf_int.1
  rw [← hf_ae.ae_integrable_condKernel_iff] at hf_int
  exact hf_int.2

/--
theorem `Integrable.norm_integral_condKernel` / 定理 `Integrable.norm_integral_condKernel`

English:
theorem Integrable.norm_integral_condKernel
  given: {f : α × Ω -> E} (hf_int : Integrable f ρ)
  proof: by
  refine hf_int.integral_norm_condKernel.mono hf_int.1.integral_condKernel.norm ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [norm_norm]
  refine (norm_integral_le_integral_norm _).trans_eq (Real.norm_of_nonneg ?_).symm
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => norm_nonneg _)

中文:
定理 可积.norm_integral_condKernel
  条件: {f : α × Ω -> E} (hf_int : 可积 f ρ)
  证明: by
  refine hf_int.integral_norm_condKernel.mono hf_int.1.integral_condKernel.norm ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [norm_norm]
  refine (norm_integral_le_integral_norm _).trans_eq (Real.norm_of_nonneg ?_).symm
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => norm_nonneg _)

Depends on / 依赖: Eventually, Filter, Filter.Eventually.of_forall, Real.norm_of_nonneg, hf_int, hf_int.integral_norm_condKernel.mono, integral_condKernel, integral_condKernel.norm, integral_nonneg_of_ae, integral_norm_condKernel, norm_integral_le_integral_norm, norm_nonneg, norm_norm, norm_of_nonneg, of_forall, trans_eq
-/
theorem Integrable.norm_integral_condKernel {f : α × Ω -> E} (hf_int : Integrable f ρ) :
    Integrable (fun x => ‖∫ y, f (x, y) ∂ρ.condKernel x‖) ρ.fst := by
  refine hf_int.integral_norm_condKernel.mono hf_int.1.integral_condKernel.norm ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [norm_norm]
  refine (norm_integral_le_integral_norm _).trans_eq (Real.norm_of_nonneg ?_).symm
  exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun y => norm_nonneg _)

/--
theorem `Integrable.integral_condKernel` / 定理 `Integrable.integral_condKernel`

English:
theorem Integrable.integral_condKernel
  given: {f : α × Ω -> E} (hf_int : Integrable f ρ)
  proof: (integrable_norm_iff hf_int.1.integral_condKernel).mp hf_int.norm_integral_condKernel

中文:
定理 可积.integral_condKernel
  条件: {f : α × Ω -> E} (hf_int : 可积 f ρ)
  证明: (integrable_norm_iff hf_int.1.integral_condKernel).mp hf_int.norm_integral_condKernel

Depends on / 依赖: hf_int, hf_int.norm_integral_condKernel, integrable_norm_iff, integral_condKernel, norm_integral_condKernel
-/
theorem Integrable.integral_condKernel {f : α × Ω -> E} (hf_int : Integrable f ρ) :
    Integrable (fun x => ∫ y, f (x, y) ∂ρ.condKernel x) ρ.fst :=
  (integrable_norm_iff hf_int.1.integral_condKernel).mp hf_int.norm_integral_condKernel

end MeasureTheory
