/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.ConditionalProbability

/-!
# Kernel associated with a conditional expectation

We define `condExpKernel μ m`, a kernel from `Ω` to `Ω` such that for all integrable functions `f`,
`μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condExpKernel μ m ω)`.

This kernel is defined if `Ω` is a standard Borel space. In general, `μ⟦s | m⟧` maps a measurable
set `s` to a function `Ω → ℝ≥0∞`, and for all `s` that map is unique up to a `μ`-null set. For all
`a`, the map from sets to `ℝ≥0∞` that we obtain that way verifies some of the properties of a
measure, but the fact that the `μ`-null set depends on `s` can prevent us from finding versions of
the conditional expectation that combine into a true measure. The standard Borel space assumption
on `Ω` allows us to do so.

## Main definitions

* `condExpKernel μ m`: kernel such that `μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condExpKernel μ m ω)`.

## Main statements

* `condExp_ae_eq_integral_condExpKernel`: `μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condExpKernel μ m ω)`.

-/

@[expose] public section


open MeasureTheory Set Filter TopologicalSpace

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

section AuxLemmas

variable {Ω F : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω -> F}

/--
theorem `_root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_id` / 定理 `_root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_id`

English:
theorem _root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_id
  statement: [TopologicalSpace F]
  proof: hf.comp_snd_map_prodMk id

中文:
定理 _root_.测度论.AEStronglyMeasurable.comp_snd_map_prod_id
  结论: [拓扑空间 F]
  证明: hf.comp_snd_map_prodMk id

Depends on / 依赖: comp_snd_map_prodMk, hf.comp_snd_map_prodMk
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_id [TopologicalSpace F]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable[m.prod mΩ] (fun x : Ω × Ω => f x.2)
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ) := hf.comp_snd_map_prodMk id

/--
theorem `_root_.MeasureTheory.Integrable.comp_snd_map_prod_id` / 定理 `_root_.MeasureTheory.Integrable.comp_snd_map_prod_id`

English:
theorem _root_.MeasureTheory.Integrable.comp_snd_map_prod_id
  statement: [NormedAddCommGroup F]
  proof: hf.comp_snd_map_prodMk id

中文:
定理 _root_.测度论.可积.comp_snd_map_prod_id
  结论: [赋范交换加群 F]
  证明: hf.comp_snd_map_prodMk id

Depends on / 依赖: comp_snd_map_prodMk, hf.comp_snd_map_prodMk
-/
theorem _root_.MeasureTheory.Integrable.comp_snd_map_prod_id [NormedAddCommGroup F]
    (hf : Integrable f μ) : Integrable (fun x : Ω × Ω => f x.2)
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ) :=
  hf.comp_snd_map_prodMk id

end AuxLemmas

variable {Ω F : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

open scoped Classical in
/-- Kernel associated with the conditional expectation with respect to a σ-algebra. It satisfies
`μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂(condExpKernel μ m ω)`.
It is defined as the conditional distribution of the identity given the identity, where the second
identity is understood as a map from `Ω` with the σ-algebra `mΩ` to `Ω` with σ-algebra `m ⊓ mΩ`.
We use `m ⊓ mΩ` instead of `m` to ensure that it is a sub-σ-algebra of `mΩ`. We then use
`Kernel.comap` to get a kernel from `m` to `mΩ` instead of from `m ⊓ mΩ` to `mΩ`. -/
noncomputable irreducible_def condExpKernel (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) : @Kernel Ω Ω m mΩ :=
  if _h : Nonempty Ω then
    Kernel.comap (@condDistrib Ω Ω Ω mΩ _ _ mΩ (m ⊓ mΩ) id id μ _) id
      (measurable_id'' (inf_le_left : m ⊓ mΩ <= m))
  else 0

/--
lemma `condExpKernel_eq` / 引理 `condExpKernel_eq`

English:
lemma condExpKernel_eq
  statement: (μ : Measure Ω) [IsFiniteMeasure μ] [h : Nonempty Ω]
  proof: by
  simp [condExpKernel, h]

中文:
引理 condExpKernel_eq
  结论: (μ : 测度 Ω) [是有限测度 μ] [h : 非空 Ω]
  证明: by
  simp [condExpKernel, h]

Depends on / 依赖: Kernel, Kernel.comap, condDistrib
-/
lemma condExpKernel_eq (μ : Measure Ω) [IsFiniteMeasure μ] [h : Nonempty Ω]
    (m : MeasurableSpace Ω) :
    condExpKernel (mΩ := mΩ) μ m = Kernel.comap (@condDistrib Ω Ω Ω mΩ _ _ mΩ (m ⊓ mΩ) id id μ _) id
      (measurable_id'' (inf_le_left : m ⊓ mΩ <= m)) := by
  simp [condExpKernel, h]

/--
lemma `condExpKernel_apply_eq_condDistrib` / 引理 `condExpKernel_apply_eq_condDistrib`

English:
lemma condExpKernel_apply_eq_condDistrib
  given: [Nonempty Ω] {ω : Ω}
  proof: by
  simp [condExpKernel_eq, Kernel.comap_apply]

中文:
引理 condExpKernel_apply_eq_condDistrib
  条件: [非空 Ω] {ω : Ω}
  证明: by
  simp [condExpKernel_eq, Kernel.comap_apply]

Depends on / 依赖: Kernel, Kernel.comap_apply, comap_apply, condExpKernel_eq
-/
lemma condExpKernel_apply_eq_condDistrib [Nonempty Ω] {ω : Ω} :
    condExpKernel μ m ω = @condDistrib Ω Ω Ω mΩ _ _ mΩ (m ⊓ mΩ) id id μ _ (id ω) := by
  simp [condExpKernel_eq, Kernel.comap_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMarkovKernel (condExpKernel μ m)
  body: by
  rcases isEmpty_or_nonempty Ω with h | h
  · exact ⟨fun a => (IsEmpty.false a).elim⟩
  · simpa [condExpKernel, h] using by infer_instance

中文:
实例 :
  签名: 是MarkovKernel (condExpKernel μ m)
  定义体: by
  rcases isEmpty_or_nonempty Ω with h | h
  · exact ⟨fun a => (IsEmpty.false a).elim⟩
  · simpa [condExpKernel, h] using by infer_instance

Depends on / 依赖: IsEmpty, IsEmpty.false, condExpKernel, infer_instance, isEmpty_or_nonempty
-/
instance : IsMarkovKernel (condExpKernel μ m) := by
  rcases isEmpty_or_nonempty Ω with h | h
  · exact ⟨fun a => (IsEmpty.false a).elim⟩
  · simpa [condExpKernel, h] using by infer_instance

/--
lemma `compProd_trim_condExpKernel` / 引理 `compProd_trim_condExpKernel`

English:
lemma compProd_trim_condExpKernel
  given: (hm : m <= mΩ)
  proof: by
  rcases isEmpty_or_nonempty Ω with h | h
  · simp [Measure.eq_zero_of_isEmpty μ]
  rw [condExpKernel_eq]; rw [trim_eq_map hm]
  have : m ⊓ mΩ = m := inf_of_le_left hm
  refine (congrArg _ (Kernel.ext fun a => Measure.ext fun s hs => ?_)).trans
    (compProd_map_condDistrib measurable_id.aemeasur

中文:
引理 compProd_trim_condExpKernel
  条件: (hm : m <= mΩ)
  证明: by
  rcases isEmpty_or_nonempty Ω with h | h
  · simp [Measure.eq_zero_of_isEmpty μ]
  rw [condExpKernel_eq]; rw [trim_eq_map hm]
  have : m ⊓ mΩ = m := inf_of_le_left hm
  refine (congrArg _ (Kernel.ext fun a => Measure.ext fun s hs => ?_)).trans
    (compProd_map_condDistrib measurable_id.aemeasur

Depends on / 依赖: Function, Function.comp_apply, Kernel, Kernel.coe_comap, Kernel.ext, Measure, Measure.eq_zero_of_isEmpty, Measure.ext, aemeasurable, coe_comap, compProd_map_condDistrib, comp_apply, condExpKernel_eq, eq_zero_of_isEmpty, id_eq, inf_of_le_left, isEmpty_or_nonempty, measurable_id, measurable_id.aemeasurable, trim_eq_map
-/
lemma compProd_trim_condExpKernel (hm : m <= mΩ) :
    (μ.trim hm) otimesₘ condExpKernel μ m
      = @Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) Function.diag μ := by
  rcases isEmpty_or_nonempty Ω with h | h
  · simp [Measure.eq_zero_of_isEmpty μ]
  rw [condExpKernel_eq]; rw [trim_eq_map hm]
  have : m ⊓ mΩ = m := inf_of_le_left hm
  refine (congrArg _ (Kernel.ext fun a => Measure.ext fun s hs => ?_)).trans
    (compProd_map_condDistrib measurable_id.aemeasurable)
  simp only [Kernel.coe_comap, Function.comp_apply, id_eq]
  congr

/--
lemma `condExpKernel_comp_trim` / 引理 `condExpKernel_comp_trim`

English:
lemma condExpKernel_comp_trim
  given: (hm : m <= mΩ)
  statement: condExpKernel μ m ∘ₘ μ.trim hm = μ
  proof: by
  rw [← Measure.snd_compProd]; rw [compProd_trim_condExpKernel]
  exact (@Measure.snd_map_prodMk Ω Ω Ω mΩ m mΩ id id μ (measurable_id'' hm)).trans Measure.map_id

中文:
引理 condExpKernel_comp_trim
  条件: (hm : m <= mΩ)
  结论: condExpKernel μ m ∘ₘ μ.trim hm = μ
  证明: by
  rw [← Measure.snd_compProd]; rw [compProd_trim_condExpKernel]
  exact (@Measure.snd_map_prodMk Ω Ω Ω mΩ m mΩ id id μ (measurable_id'' hm)).trans Measure.map_id

Depends on / 依赖: Measure, Measure.map_id, Measure.snd_compProd, Measure.snd_map_prodMk, compProd_trim_condExpKernel, map_id, measurable_id, snd_compProd, snd_map_prodMk
-/
lemma condExpKernel_comp_trim (hm : m <= mΩ) : condExpKernel μ m ∘ₘ μ.trim hm = μ := by
  rw [← Measure.snd_compProd]; rw [compProd_trim_condExpKernel]
  exact (@Measure.snd_map_prodMk Ω Ω Ω mΩ m mΩ id id μ (measurable_id'' hm)).trans Measure.map_id

section Measurability

variable [NormedAddCommGroup F] {f : Ω -> F}

/--
theorem `measurable_condExpKernel` / 定理 `measurable_condExpKernel`

English:
theorem measurable_condExpKernel
  given: {s : Set Ω} (hs : MeasurableSet s)
  proof: (condExpKernel μ m).measurable_coe hs

中文:
定理 measurable_condExpKernel
  条件: {s : 集合 Ω} (hs : 可测集 s)
  证明: (condExpKernel μ m).measurable_coe hs

Depends on / 依赖: condExpKernel, measurable_coe
-/
theorem measurable_condExpKernel {s : Set Ω} (hs : MeasurableSet s) :
    Measurable[m] fun ω => condExpKernel μ m ω s :=
  (condExpKernel μ m).measurable_coe hs

/--
theorem `stronglyMeasurable_condExpKernel` / 定理 `stronglyMeasurable_condExpKernel`

English:
theorem stronglyMeasurable_condExpKernel
  given: {s : Set Ω} (hs : MeasurableSet s)
  proof: Measurable.stronglyMeasurable (measurable_condExpKernel hs)

中文:
定理 stronglyMeasurable_condExpKernel
  条件: {s : 集合 Ω} (hs : 可测集 s)
  证明: Measurable.stronglyMeasurable (measurable_condExpKernel hs)

Depends on / 依赖: Measurable, Measurable.stronglyMeasurable, measurable_condExpKernel, stronglyMeasurable
-/
theorem stronglyMeasurable_condExpKernel {s : Set Ω} (hs : MeasurableSet s) :
    StronglyMeasurable[m] fun ω => condExpKernel μ m ω s :=
  Measurable.stronglyMeasurable (measurable_condExpKernel hs)

/--
theorem `_root_.MeasureTheory.StronglyMeasurable.integral_condExpKernel'` / 定理 `_root_.MeasureTheory.StronglyMeasurable.integral_condExpKernel'`

English:
theorem _root_.MeasureTheory.StronglyMeasurable.integral_condExpKernel'
  statement: [NormedSpace Real F]
  proof: by
  nontriviality Ω
  simp_rw [condExpKernel_apply_eq_condDistrib]
  exact (hf.comp_measurable measurable_snd).integral_condDistrib

中文:
定理 _root_.测度论.StronglyMeasurable.integral_condExpKernel'
  结论: [赋范空间 实数 F]
  证明: by
  nontriviality Ω
  simp_rw [condExpKernel_apply_eq_condDistrib]
  exact (hf.comp_measurable measurable_snd).integral_condDistrib

Depends on / 依赖: comp_measurable, condExpKernel_apply_eq_condDistrib, hf.comp_measurable, integral_condDistrib, measurable_snd, nontriviality, simp_rw
-/
theorem _root_.MeasureTheory.StronglyMeasurable.integral_condExpKernel' [NormedSpace Real F]
    (hf : StronglyMeasurable f) :
    StronglyMeasurable[m ⊓ mΩ] (fun ω => ∫ y, f y ∂condExpKernel μ m ω) := by
  nontriviality Ω
  simp_rw [condExpKernel_apply_eq_condDistrib]
  exact (hf.comp_measurable measurable_snd).integral_condDistrib

/--
theorem `_root_.MeasureTheory.StronglyMeasurable.integral_condExpKernel` / 定理 `_root_.MeasureTheory.StronglyMeasurable.integral_condExpKernel`

English:
theorem _root_.MeasureTheory.StronglyMeasurable.integral_condExpKernel
  statement: [NormedSpace Real F]
  proof: hf.integral_condExpKernel'.mono inf_le_left

中文:
定理 _root_.测度论.StronglyMeasurable.integral_condExpKernel
  结论: [赋范空间 实数 F]
  证明: hf.integral_condExpKernel'.mono inf_le_left

Depends on / 依赖: hf.integral_condExpKernel, inf_le_left, integral_condExpKernel
-/
theorem _root_.MeasureTheory.StronglyMeasurable.integral_condExpKernel [NormedSpace Real F]
    (hf : StronglyMeasurable f) :
    StronglyMeasurable[m] (fun ω => ∫ y, f y ∂condExpKernel μ m ω) :=
  hf.integral_condExpKernel'.mono inf_le_left

/--
theorem `_root_.MeasureTheory.AEStronglyMeasurable.integral_condExpKernel` / 定理 `_root_.MeasureTheory.AEStronglyMeasurable.integral_condExpKernel`

English:
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condExpKernel
  statement: [NormedSpace Real F]
  proof: by
  nontriviality Ω
  simp_rw [condExpKernel_apply_eq_condDistrib]
  exact AEStronglyMeasurable.integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ)) aemeasurable_id
    hf.comp_snd_map_prod_id

中文:
定理 _root_.测度论.AEStronglyMeasurable.integral_condExpKernel
  结论: [赋范空间 实数 F]
  证明: by
  nontriviality Ω
  simp_rw [condExpKernel_apply_eq_condDistrib]
  exact AEStronglyMeasurable.integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ)) aemeasurable_id
    hf.comp_snd_map_prod_id

Depends on / 依赖: AEStronglyMeasurable, AEStronglyMeasurable.integral_condDistrib, aemeasurable_id, comp_snd_map_prod_id, condExpKernel_apply_eq_condDistrib, hf.comp_snd_map_prod_id, inf_le_right, integral_condDistrib, nontriviality, simp_rw
-/
theorem _root_.MeasureTheory.AEStronglyMeasurable.integral_condExpKernel [NormedSpace Real F]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun ω => ∫ y, f y ∂condExpKernel μ m ω) μ := by
  nontriviality Ω
  simp_rw [condExpKernel_apply_eq_condDistrib]
  exact AEStronglyMeasurable.integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ)) aemeasurable_id
    hf.comp_snd_map_prod_id

/--
theorem `aestronglyMeasurable_integral_condExpKernel` / 定理 `aestronglyMeasurable_integral_condExpKernel`

English:
theorem aestronglyMeasurable_integral_condExpKernel
  statement: [NormedSpace Real F]
  proof: by
  nontriviality Ω
  rw [condExpKernel_eq]
  have h := aestronglyMeasurable_integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ)) aemeasurable_id hf.comp_snd_map_prod_id
  rw [MeasurableSpace.comap_id] at h
  exact h.mono inf_le_left

中文:
定理 aestronglyMeasurable_integral_condExpKernel
  结论: [赋范空间 实数 F]
  证明: by
  nontriviality Ω
  rw [condExpKernel_eq]
  have h := aestronglyMeasurable_integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ)) aemeasurable_id hf.comp_snd_map_prod_id
  rw [MeasurableSpace.comap_id] at h
  exact h.mono inf_le_left

Depends on / 依赖: MeasurableSpace, MeasurableSpace.comap_id, aemeasurable_id, aestronglyMeasurable_integral_condDistrib, comap_id, comp_snd_map_prod_id, condExpKernel_eq, h.mono, hf.comp_snd_map_prod_id, inf_le_left, inf_le_right, nontriviality
-/
theorem aestronglyMeasurable_integral_condExpKernel [NormedSpace Real F]
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable[m] (fun ω => ∫ y, f y ∂condExpKernel μ m ω) μ := by
  nontriviality Ω
  rw [condExpKernel_eq]
  have h := aestronglyMeasurable_integral_condDistrib
    (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ)) aemeasurable_id hf.comp_snd_map_prod_id
  rw [MeasurableSpace.comap_id] at h
  exact h.mono inf_le_left

/--
lemma `aestronglyMeasurable_trim_condExpKernel` / 引理 `aestronglyMeasurable_trim_condExpKernel`

English:
lemma aestronglyMeasurable_trim_condExpKernel
  given: (hm : m <= mΩ) (hf : AEStronglyMeasurable f μ)
  proof: by
  refine Measure.ae_ae_of_ae_comp ?_
  rw [condExpKernel_comp_trim hm]
  exact hf.ae_eq_mk

中文:
引理 aestronglyMeasurable_trim_condExpKernel
  条件: (hm : m <= mΩ) (hf : AEStronglyMeasurable f μ)
  证明: by
  refine Measure.ae_ae_of_ae_comp ?_
  rw [condExpKernel_comp_trim hm]
  exact hf.ae_eq_mk

Depends on / 依赖: Measure, Measure.ae_ae_of_ae_comp, ae_ae_of_ae_comp, ae_eq_mk, condExpKernel_comp_trim, hf.ae_eq_mk
-/
lemma aestronglyMeasurable_trim_condExpKernel (hm : m <= mΩ) (hf : AEStronglyMeasurable f μ) :
    forallᵐ ω ∂(μ.trim hm), f =ᵐ[condExpKernel μ m ω] hf.mk f := by
  refine Measure.ae_ae_of_ae_comp ?_
  rw [condExpKernel_comp_trim hm]
  exact hf.ae_eq_mk

end Measurability

section Integrability

variable [NormedAddCommGroup F] {f : Ω -> F}

/--
theorem `_root_.MeasureTheory.Integrable.condExpKernel_ae` / 定理 `_root_.MeasureTheory.Integrable.condExpKernel_ae`

English:
theorem _root_.MeasureTheory.Integrable.condExpKernel_ae
  given: (hf_int : Integrable f μ)
  proof: by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.condDistrib_ae (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ)) aemeasurable_id
      hf_int.comp_snd_map_prod_id using 1

中文:
定理 _root_.测度论.可积.condExpKernel_ae
  条件: (hf_int : 可积 f μ)
  证明: by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.condDistrib_ae (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ)) aemeasurable_id
      hf_int.comp_snd_map_prod_id using 1

Depends on / 依赖: Integrable, Integrable.condDistrib_ae, aemeasurable_id, comp_snd_map_prod_id, condDistrib_ae, condExpKernel_eq, convert, hf_int, hf_int.comp_snd_map_prod_id, inf_le_right, nontriviality
-/
theorem _root_.MeasureTheory.Integrable.condExpKernel_ae (hf_int : Integrable f μ) :
    forallᵐ ω ∂μ, Integrable f (condExpKernel μ m ω) := by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.condDistrib_ae (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ)) aemeasurable_id
      hf_int.comp_snd_map_prod_id using 1

/--
theorem `_root_.MeasureTheory.Integrable.integral_norm_condExpKernel` / 定理 `_root_.MeasureTheory.Integrable.integral_norm_condExpKernel`

English:
theorem _root_.MeasureTheory.Integrable.integral_norm_condExpKernel
  given: (hf_int : Integrable f μ)
  proof: by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.integral_norm_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ))
      aemeasurable_id hf_int.comp_snd_map_prod_id using 1

中文:
定理 _root_.测度论.可积.integral_norm_condExpKernel
  条件: (hf_int : 可积 f μ)
  证明: by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.integral_norm_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ))
      aemeasurable_id hf_int.comp_snd_map_prod_id using 1

Depends on / 依赖: Integrable, Integrable.integral_norm_condDistrib, aemeasurable_id, comp_snd_map_prod_id, condExpKernel_eq, convert, hf_int, hf_int.comp_snd_map_prod_id, inf_le_right, integral_norm_condDistrib, nontriviality
-/
theorem _root_.MeasureTheory.Integrable.integral_norm_condExpKernel (hf_int : Integrable f μ) :
    Integrable (fun ω => ∫ y, ‖f y‖ ∂condExpKernel μ m ω) μ := by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.integral_norm_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ))
      aemeasurable_id hf_int.comp_snd_map_prod_id using 1

/--
theorem `_root_.MeasureTheory.Integrable.norm_integral_condExpKernel` / 定理 `_root_.MeasureTheory.Integrable.norm_integral_condExpKernel`

English:
theorem _root_.MeasureTheory.Integrable.norm_integral_condExpKernel
  statement: [NormedSpace Real F]
  proof: by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.norm_integral_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ))
      aemeasurable_id hf_int.comp_snd_map_prod_id using 1

中文:
定理 _root_.测度论.可积.norm_integral_condExpKernel
  结论: [赋范空间 实数 F]
  证明: by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.norm_integral_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ))
      aemeasurable_id hf_int.comp_snd_map_prod_id using 1

Depends on / 依赖: Integrable, Integrable.norm_integral_condDistrib, aemeasurable_id, comp_snd_map_prod_id, condExpKernel_eq, convert, hf_int, hf_int.comp_snd_map_prod_id, inf_le_right, nontriviality, norm_integral_condDistrib
-/
theorem _root_.MeasureTheory.Integrable.norm_integral_condExpKernel [NormedSpace Real F]
    (hf_int : Integrable f μ) :
    Integrable (fun ω => ‖∫ y, f y ∂condExpKernel μ m ω‖) μ := by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.norm_integral_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ))
      aemeasurable_id hf_int.comp_snd_map_prod_id using 1

/--
theorem `_root_.MeasureTheory.Integrable.integral_condExpKernel` / 定理 `_root_.MeasureTheory.Integrable.integral_condExpKernel`

English:
theorem _root_.MeasureTheory.Integrable.integral_condExpKernel
  statement: [NormedSpace Real F]
  proof: by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.integral_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ))
      aemeasurable_id hf_int.comp_snd_map_prod_id using 1

中文:
定理 _root_.测度论.可积.integral_condExpKernel
  结论: [赋范空间 实数 F]
  证明: by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.integral_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ))
      aemeasurable_id hf_int.comp_snd_map_prod_id using 1

Depends on / 依赖: Integrable, Integrable.integral_condDistrib, aemeasurable_id, comp_snd_map_prod_id, condExpKernel_eq, convert, hf_int, hf_int.comp_snd_map_prod_id, inf_le_right, integral_condDistrib, nontriviality
-/
theorem _root_.MeasureTheory.Integrable.integral_condExpKernel [NormedSpace Real F]
    (hf_int : Integrable f μ) :
    Integrable (fun ω => ∫ y, f y ∂condExpKernel μ m ω) μ := by
  nontriviality Ω
  rw [condExpKernel_eq]
  convert!
    Integrable.integral_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ))
      aemeasurable_id hf_int.comp_snd_map_prod_id using 1

/--
theorem `integrable_toReal_condExpKernel` / 定理 `integrable_toReal_condExpKernel`

English:
theorem integrable_toReal_condExpKernel
  given: {s : Set Ω} (hs : MeasurableSet s)
  proof: by
  nontriviality Ω
  rw [condExpKernel_eq]
  exact integrable_toReal_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ)) hs

中文:
定理 integrable_to实数_condExpKernel
  条件: {s : 集合 Ω} (hs : 可测集 s)
  证明: by
  nontriviality Ω
  rw [condExpKernel_eq]
  exact integrable_toReal_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ)) hs

Depends on / 依赖: aemeasurable_id, condExpKernel_eq, inf_le_right, integrable_toReal_condDistrib, nontriviality
-/
theorem integrable_toReal_condExpKernel {s : Set Ω} (hs : MeasurableSet s) :
    Integrable (fun ω => (condExpKernel μ m ω).real s) μ := by
  nontriviality Ω
  rw [condExpKernel_eq]
  exact integrable_toReal_condDistrib (aemeasurable_id'' μ (inf_le_right : m ⊓ mΩ <= mΩ)) hs

end Integrability

/--
lemma `condExpKernel_ae_eq_condExp'` / 引理 `condExpKernel_ae_eq_condExp'`

English:
lemma condExpKernel_ae_eq_condExp'
  given: {s : Set Ω} (hs : MeasurableSet s)
  proof: by
  rcases isEmpty_or_nonempty Ω with h | h
  · have : μ = 0 := Measure.eq_zero_of_isEmpty μ
    simpa [this] using! trivial
  have h := condDistrib_ae_eq_condExp (μ := μ)
    (measurable_id'' (inf_le_right : m ⊓ mΩ <= mΩ)) measurable_id hs
  simp only [id_eq, MeasurableSpace.comap_id, preimage_id_

中文:
引理 condExpKernel_ae_eq_condExp'
  条件: {s : 集合 Ω} (hs : 可测集 s)
  证明: by
  rcases isEmpty_or_nonempty Ω with h | h
  · have : μ = 0 := Measure.eq_zero_of_isEmpty μ
    simpa [this] using! trivial
  have h := condDistrib_ae_eq_condExp (μ := μ)
    (measurable_id'' (inf_le_right : m ⊓ mΩ <= mΩ)) measurable_id hs
  simp only [id_eq, MeasurableSpace.comap_id, preimage_id_

Depends on / 依赖: MeasurableSpace, MeasurableSpace.comap_id, Measure, Measure.eq_zero_of_isEmpty, comap_id, condDistrib_ae_eq_condExp, condExpKernel_apply_eq_condDistrib, eq_zero_of_isEmpty, id_eq, inf_le_right, isEmpty_or_nonempty, measurable_id, preimage_id_eq, simp_rw
-/
lemma condExpKernel_ae_eq_condExp' {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω => (condExpKernel μ m ω).real s) =ᵐ[μ] μ⟦s | m ⊓ mΩ⟧ := by
  rcases isEmpty_or_nonempty Ω with h | h
  · have : μ = 0 := Measure.eq_zero_of_isEmpty μ
    simpa [this] using! trivial
  have h := condDistrib_ae_eq_condExp (μ := μ)
    (measurable_id'' (inf_le_right : m ⊓ mΩ <= mΩ)) measurable_id hs
  simp only [id_eq, MeasurableSpace.comap_id, preimage_id_eq] at h
  simp_rw [condExpKernel_apply_eq_condDistrib]
  exact h

/--
lemma `condExpKernel_ae_eq_condExp` / 引理 `condExpKernel_ae_eq_condExp`

English:
lemma condExpKernel_ae_eq_condExp
  proof: (condExpKernel_ae_eq_condExp' hs).trans (by rw [inf_of_le_left hm])

中文:
引理 condExpKernel_ae_eq_condExp
  证明: (condExpKernel_ae_eq_condExp' hs).trans (by rw [inf_of_le_left hm])

Depends on / 依赖: condExpKernel_ae_eq_condExp, inf_of_le_left
-/
lemma condExpKernel_ae_eq_condExp
    (hm : m <= mΩ) {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω => (condExpKernel μ m ω).real s) =ᵐ[μ] μ⟦s | m⟧ :=
  (condExpKernel_ae_eq_condExp' hs).trans (by rw [inf_of_le_left hm])

/--
lemma `condExpKernel_ae_eq_trim_condExp` / 引理 `condExpKernel_ae_eq_trim_condExp`

English:
lemma condExpKernel_ae_eq_trim_condExp
  proof: by
  simp_rw [measureReal_def]
  rw [(measurable_condExpKernel hs).ennreal_toReal.stronglyMeasurable.ae_eq_trim_iff hm
    stronglyMeasurable_condExp]
  exact condExpKernel_ae_eq_condExp hm hs

中文:
引理 condExpKernel_ae_eq_trim_condExp
  证明: by
  simp_rw [measureReal_def]
  rw [(measurable_condExpKernel hs).ennreal_toReal.stronglyMeasurable.ae_eq_trim_iff hm
    stronglyMeasurable_condExp]
  exact condExpKernel_ae_eq_condExp hm hs

Depends on / 依赖: ae_eq_trim_iff, condExpKernel_ae_eq_condExp, ennreal_toReal, ennreal_toReal.stronglyMeasurable.ae_eq_trim_iff, measurable_condExpKernel, measureReal_def, simp_rw, stronglyMeasurable, stronglyMeasurable_condExp
-/
lemma condExpKernel_ae_eq_trim_condExp
    (hm : m <= mΩ) {s : Set Ω} (hs : MeasurableSet s) :
    (fun ω => (condExpKernel μ m ω).real s) =ᵐ[μ.trim hm] μ⟦s | m⟧ := by
  simp_rw [measureReal_def]
  rw [(measurable_condExpKernel hs).ennreal_toReal.stronglyMeasurable.ae_eq_trim_iff hm
    stronglyMeasurable_condExp]
  exact condExpKernel_ae_eq_condExp hm hs

/--
lemma `condDistrib_apply_ae_eq_condExpKernel_map` / 引理 `condDistrib_apply_ae_eq_condExpKernel_map`

English:
lemma condDistrib_apply_ae_eq_condExpKernel_map
  statement: {β γ : Type*} {mβ : MeasurableSpace β}
  proof: by
  simp_rw [Kernel.map_apply' _ hX _ hs]
  filter_upwards [condDistrib_ae_eq_condExp hY hX (μ := μ) hs,
    condExpKernel_ae_eq_condExp hY.comap_le (μ := μ) (hX hs)] with a ha₁ ha₂
  rw [← measureReal_eq_measureReal_iff]; rw [ha₁]; rw [ha₂]

中文:
引理 condDistrib_apply_ae_eq_condExpKernel_map
  结论: {β γ : 类型} {mβ : 可测空间 β}
  证明: by
  simp_rw [Kernel.map_apply' _ hX _ hs]
  filter_upwards [condDistrib_ae_eq_condExp hY hX (μ := μ) hs,
    condExpKernel_ae_eq_condExp hY.comap_le (μ := μ) (hX hs)] with a ha₁ ha₂
  rw [← measureReal_eq_measureReal_iff]; rw [ha₁]; rw [ha₂]

Depends on / 依赖: Kernel, Kernel.map_apply, comap_le, condDistrib_ae_eq_condExp, condExpKernel_ae_eq_condExp, filter_upwards, hY.comap_le, map_apply, measureReal_eq_measureReal_iff, simp_rw
-/
lemma condDistrib_apply_ae_eq_condExpKernel_map {β γ : Type*} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} [StandardBorelSpace β] [Nonempty β] {X : Ω -> β} {Y : Ω -> γ}
    (hX : Measurable X) (hY : Measurable Y) {s : Set β} (hs : MeasurableSet s) :
    (fun a => condDistrib X Y μ (Y a) s)
      =ᵐ[μ] fun a => (condExpKernel μ (mγ.comap Y)).map X a s := by
  simp_rw [Kernel.map_apply' _ hX _ hs]
  filter_upwards [condDistrib_ae_eq_condExp hY hX (μ := μ) hs,
    condExpKernel_ae_eq_condExp hY.comap_le (μ := μ) (hX hs)] with a ha₁ ha₂
  rw [← measureReal_eq_measureReal_iff]; rw [ha₁]; rw [ha₂]

/--
theorem `condExp_ae_eq_integral_condExpKernel'` / 定理 `condExp_ae_eq_integral_condExpKernel'`

English:
theorem condExp_ae_eq_integral_condExpKernel'
  statement: [NormedAddCommGroup F] {f : Ω -> F}
  proof: by
  rcases isEmpty_or_nonempty Ω with h | h
  · have : μ = 0 := Measure.eq_zero_of_isEmpty μ
    simpa [this] using! trivial
  have hX : @Measurable Ω Ω mΩ (m ⊓ mΩ) id := measurable_id.mono le_rfl (inf_le_right : m ⊓ mΩ <= mΩ)
  simp_rw [condExpKernel_apply_eq_condDistrib]
  have h := condExp_ae_eq

中文:
定理 condExp_ae_eq_integral_condExpKernel'
  结论: [赋范交换加群 F] {f : Ω -> F}
  证明: by
  rcases isEmpty_or_nonempty Ω with h | h
  · have : μ = 0 := Measure.eq_zero_of_isEmpty μ
    simpa [this] using! trivial
  have hX : @Measurable Ω Ω mΩ (m ⊓ mΩ) id := measurable_id.mono le_rfl (inf_le_right : m ⊓ mΩ <= mΩ)
  simp_rw [condExpKernel_apply_eq_condDistrib]
  have h := condExp_ae_eq

Depends on / 依赖: Measurable, MeasurableSpace, MeasurableSpace.comap_id, Measure, Measure.eq_zero_of_isEmpty, comap_id, condExpKernel_apply_eq_condDistrib, condExp_ae_eq_integral_condDistrib_id, eq_zero_of_isEmpty, hf_int, id_eq, inf_le_right, isEmpty_or_nonempty, le_rfl, measurable_id, measurable_id.mono, simp_rw
-/
theorem condExp_ae_eq_integral_condExpKernel' [NormedAddCommGroup F] {f : Ω -> F}
    [NormedSpace Real F] [CompleteSpace F] (hf_int : Integrable f μ) :
    μ[f | m ⊓ mΩ] =ᵐ[μ] fun ω => ∫ y, f y ∂condExpKernel μ m ω := by
  rcases isEmpty_or_nonempty Ω with h | h
  · have : μ = 0 := Measure.eq_zero_of_isEmpty μ
    simpa [this] using! trivial
  have hX : @Measurable Ω Ω mΩ (m ⊓ mΩ) id := measurable_id.mono le_rfl (inf_le_right : m ⊓ mΩ <= mΩ)
  simp_rw [condExpKernel_apply_eq_condDistrib]
  have h := condExp_ae_eq_integral_condDistrib_id hX hf_int
  simpa only [MeasurableSpace.comap_id, id_eq] using! h

/--
theorem `condExp_ae_eq_integral_condExpKernel` / 定理 `condExp_ae_eq_integral_condExpKernel`

English:
theorem condExp_ae_eq_integral_condExpKernel
  statement: [NormedAddCommGroup F] {f : Ω -> F}
  proof: ((condExp_ae_eq_integral_condExpKernel' hf_int).symm.trans (by rw [inf_of_le_left hm])).symm

中文:
定理 condExp_ae_eq_integral_condExpKernel
  结论: [赋范交换加群 F] {f : Ω -> F}
  证明: ((condExp_ae_eq_integral_condExpKernel' hf_int).symm.trans (by rw [inf_of_le_left hm])).symm

Depends on / 依赖: condExp_ae_eq_integral_condExpKernel, hf_int, inf_of_le_left, symm.trans
-/
theorem condExp_ae_eq_integral_condExpKernel [NormedAddCommGroup F] {f : Ω -> F}
    [NormedSpace Real F] [CompleteSpace F] (hm : m <= mΩ) (hf_int : Integrable f μ) :
    μ[f | m] =ᵐ[μ] fun ω => ∫ y, f y ∂condExpKernel μ m ω :=
  ((condExp_ae_eq_integral_condExpKernel' hf_int).symm.trans (by rw [inf_of_le_left hm])).symm

/--
theorem `condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable` / 定理 `condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable`

English:
theorem condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable
  proof: by
  refine StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm ?_ ?_ ?_
  · exact stronglyMeasurable_condExp
  · exact hf.integral_condExpKernel
  · exact condExp_ae_eq_integral_condExpKernel hm hf_int

中文:
定理 condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable
  证明: by
  refine StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm ?_ ?_ ?_
  · exact stronglyMeasurable_condExp
  · exact hf.integral_condExpKernel
  · exact condExp_ae_eq_integral_condExpKernel hm hf_int

Depends on / 依赖: StronglyMeasurable, StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable, ae_eq_trim_of_stronglyMeasurable, condExp_ae_eq_integral_condExpKernel, hf.integral_condExpKernel, hf_int, integral_condExpKernel, stronglyMeasurable_condExp
-/
theorem condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable
    [NormedAddCommGroup F] {f : Ω -> F} [NormedSpace Real F] [CompleteSpace F]
    (hm : m <= mΩ) (hf : StronglyMeasurable f) (hf_int : Integrable f μ) :
    μ[f | m] =ᵐ[μ.trim hm] fun ω => ∫ y, f y ∂condExpKernel μ m ω := by
  refine StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm ?_ ?_ ?_
  · exact stronglyMeasurable_condExp
  · exact hf.integral_condExpKernel
  · exact condExp_ae_eq_integral_condExpKernel hm hf_int

/--
theorem `condExp_ae_eq_trim_integral_condExpKernel` / 定理 `condExp_ae_eq_trim_integral_condExpKernel`

English:
theorem condExp_ae_eq_trim_integral_condExpKernel
  statement: [NormedAddCommGroup F] {f : Ω -> F}
  proof: by
  refine (condExp_congr_ae_trim hm hf_int.1.ae_eq_mk).trans ?_
  refine (condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable hm
    hf_int.1.stronglyMeasurable_mk ?_).trans ?_
  · rwa [integrable_congr hf_int.1.ae_eq_mk.symm]
  filter_upwards [aestronglyMeasurable_trim_condExpKernel h

中文:
定理 condExp_ae_eq_trim_integral_condExpKernel
  结论: [赋范交换加群 F] {f : Ω -> F}
  证明: by
  refine (condExp_congr_ae_trim hm hf_int.1.ae_eq_mk).trans ?_
  refine (condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable hm
    hf_int.1.stronglyMeasurable_mk ?_).trans ?_
  · rwa [integrable_congr hf_int.1.ae_eq_mk.symm]
  filter_upwards [aestronglyMeasurable_trim_condExpKernel h

Depends on / 依赖: ae_eq_mk, ae_eq_mk.symm, aestronglyMeasurable_trim_condExpKernel, condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable, condExp_congr_ae_trim, filter_upwards, hf_int, integrable_congr, integral_congr_ae, stronglyMeasurable_mk
-/
theorem condExp_ae_eq_trim_integral_condExpKernel [NormedAddCommGroup F] {f : Ω -> F}
    [NormedSpace Real F] [CompleteSpace F] (hm : m <= mΩ) (hf_int : Integrable f μ) :
    μ[f | m] =ᵐ[μ.trim hm] fun ω => ∫ y, f y ∂condExpKernel μ m ω := by
  refine (condExp_congr_ae_trim hm hf_int.1.ae_eq_mk).trans ?_
  refine (condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable hm
    hf_int.1.stronglyMeasurable_mk ?_).trans ?_
  · rwa [integrable_congr hf_int.1.ae_eq_mk.symm]
  filter_upwards [aestronglyMeasurable_trim_condExpKernel hm hf_int.1] with ω hω
  rw [integral_congr_ae hω]

section Cond

/-! ### Relation between conditional expectation, conditional kernel and the conditional measure. -/

open MeasurableSpace

variable {s t : Set Ω} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]

omit [StandardBorelSpace Ω]

/--
lemma `condExp_generateFrom_singleton` / 引理 `condExp_generateFrom_singleton`

English:
lemma condExp_generateFrom_singleton
  given: (hs : MeasurableSet s) {f : Ω -> F} (hf : Integrable f μ)
  proof: by
  by_cases hμs : μ s = 0
  · rw [Measure.restrict_eq_zero.2 hμs]
    rfl
  refine ae_eq_trans (condExp_restrict_ae_eq_restrict
    (generateFrom_singleton_le hs)
    (measurableSet_generateFrom rfl) hf).symm ?_
  · refine (ae_eq_condExp_of_forall_setIntegral_eq (generateFrom_singleton_le hs) hf.r

中文:
引理 condExp_generateFrom_singleton
  条件: (hs : 可测集 s) {f : Ω -> F} (hf : 可积 f μ)
  证明: by
  by_cases hμs : μ s = 0
  · rw [Measure.restrict_eq_zero.2 hμs]
    rfl
  refine ae_eq_trans (condExp_restrict_ae_eq_restrict
    (generateFrom_singleton_le hs)
    (measurableSet_generateFrom rfl) hf).symm ?_
  · refine (ae_eq_condExp_of_forall_setIntegral_eq (generateFrom_singleton_le hs) hf.r

Depends on / 依赖: Measure, Measure.restrict_eq_zero, Or.inr, ae_eq_condExp_of_forall_setIntegral_eq, ae_eq_trans, aestronglyMeasurable, condExp_restrict_ae_eq_restrict, generateFrom_singleton_le, hf.restrict, integrableOn_const_iff, measurableSet_generateFr, measurableSet_generateFrom, measure_lt_top, restrict, restrict_eq_zero, stronglyMeasurable_const, stronglyMeasurable_const.aestronglyMeasurable
-/
lemma condExp_generateFrom_singleton (hs : MeasurableSet s) {f : Ω -> F} (hf : Integrable f μ) :
    μ[f | generateFrom {s}] =ᵐ[μ.restrict s] fun _ => ∫ x, f x ∂μ[|s] := by
  by_cases hμs : μ s = 0
  · rw [Measure.restrict_eq_zero.2 hμs]
    rfl
  refine ae_eq_trans (condExp_restrict_ae_eq_restrict
    (generateFrom_singleton_le hs)
    (measurableSet_generateFrom rfl) hf).symm ?_
  · refine (ae_eq_condExp_of_forall_setIntegral_eq (generateFrom_singleton_le hs) hf.restrict ?_ ?_
      stronglyMeasurable_const.aestronglyMeasurable).symm
    · rintro t - -
      rw [integrableOn_const_iff]
exact Or.inr measure_lt_top (μ.restrict s) t
    · rintro t ht -
      obtain (h | h | h | h) := measurableSet_generateFrom_singleton_iff.1 ht
      · simp [h]
      · simp only [h, cond, integral_smul_measure, ENNReal.toReal_inv, integral_const,
        MeasurableSet.univ, measureReal_restrict_apply, univ_inter, measureReal_restrict_apply_self,
        ← measureReal_def]
        rw [smul_inv_smul₀]; rw [Measure.restrict_restrict hs]; rw [inter_self]
        exact ENNReal.toReal_ne_zero.2 ⟨hμs, measure_ne_top _ _⟩
      · simp only [h, integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
          measureReal_restrict_apply hs.compl, compl_inter_self, measureReal_empty, zero_smul,
          ((Measure.restrict_apply_eq_zero hs.compl).2 <| compl_inter_self s ▸ measure_empty),
          setIntegral_measure_zero]
      · simp only [h, Measure.restrict_univ, cond, integral_smul_measure, ENNReal.toReal_inv, ←
        measureReal_def, integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter]
        rw [smul_inv_smul₀]
        exact (measureReal_ne_zero_iff (by finiteness)).2 hμs

/--
lemma `condExp_set_generateFrom_singleton` / 引理 `condExp_set_generateFrom_singleton`

English:
lemma condExp_set_generateFrom_singleton
  given: (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  rw [← integral_indicator_one ht]
exact condExp_generateFrom_singleton hs Integrable.indicator (integrable_const 1) ht

中文:
引理 condExp_set_generateFrom_singleton
  条件: (hs : 可测集 s) (ht : 可测集 t)
  证明: by
  rw [← integral_indicator_one ht]
exact condExp_generateFrom_singleton hs Integrable.indicator (integrable_const 1) ht

Depends on / 依赖: Integrable, Integrable.indicator, condExp_generateFrom_singleton, indicator, integrable_const, integral_indicator_one
-/
lemma condExp_set_generateFrom_singleton (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ⟦t | generateFrom {s}⟧ =ᵐ[μ.restrict s] fun _ => μ[|s].real t := by
  rw [← integral_indicator_one ht]
exact condExp_generateFrom_singleton hs Integrable.indicator (integrable_const 1) ht

/--
lemma `condExpKernel_singleton_ae_eq_cond` / 引理 `condExpKernel_singleton_ae_eq_cond`

English:
lemma condExpKernel_singleton_ae_eq_cond
  statement: [StandardBorelSpace Ω] (hs : MeasurableSet s)
  proof: by
  have : (fun ω => (condExpKernel μ (generateFrom {s}) ω).real t) =ᵐ[μ.restrict s]
      μ⟦t | generateFrom {s}⟧ :=
ae_restrict_le condExpKernel_ae_eq_condExp
      (generateFrom_singleton_le hs) ht
  filter_upwards [condExp_set_generateFrom_singleton hs ht, this] with ω hω₁ hω₂
  rwa [hω₁, measu

中文:
引理 condExpKernel_singleton_ae_eq_cond
  结论: [StandardBorel空间 Ω] (hs : 可测集 s)
  证明: by
  have : (fun ω => (condExpKernel μ (generateFrom {s}) ω).real t) =ᵐ[μ.restrict s]
      μ⟦t | generateFrom {s}⟧ :=
ae_restrict_le condExpKernel_ae_eq_condExp
      (generateFrom_singleton_le hs) ht
  filter_upwards [condExp_set_generateFrom_singleton hs ht, this] with ω hω₁ hω₂
  rwa [hω₁, measu

Depends on / 依赖: ENNReal, ENNReal.toReal_eq_toReal_iff, ae_restrict_le, condExpKernel, condExpKernel_ae_eq_condExp, condExp_set_generateFrom_singleton, filter_upwards, generateFrom, generateFrom_singleton_le, measureReal_def, measure_ne_top, restrict, toReal_eq_toReal_iff
-/
lemma condExpKernel_singleton_ae_eq_cond [StandardBorelSpace Ω] (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    forallᵐ ω ∂μ.restrict s,
      condExpKernel μ (generateFrom {s}) ω t = μ[t | s] := by
  have : (fun ω => (condExpKernel μ (generateFrom {s}) ω).real t) =ᵐ[μ.restrict s]
      μ⟦t | generateFrom {s}⟧ :=
ae_restrict_le condExpKernel_ae_eq_condExp
      (generateFrom_singleton_le hs) ht
  filter_upwards [condExp_set_generateFrom_singleton hs ht, this] with ω hω₁ hω₂
  rwa [hω₁, measureReal_def, measureReal_def,
    ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ t) (measure_ne_top _ t)] at hω₂

end Cond

end ProbabilityTheory
