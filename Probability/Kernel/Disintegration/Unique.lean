/-
Copyright (c) 2023 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Disintegration.Integral

/-!
# Uniqueness of the conditional kernel

We prove that the conditional kernels `ProbabilityTheory.Kernel.condKernel` and
`MeasureTheory.Measure.condKernel` are almost everywhere unique.

## Main statements

* `ProbabilityTheory.eq_condKernel_of_kernel_eq_compProd`: a.e. uniqueness of
  `ProbabilityTheory.Kernel.condKernel`
* `ProbabilityTheory.eq_condKernel_of_measure_eq_compProd`: a.e. uniqueness of
  `MeasureTheory.Measure.condKernel`
* `ProbabilityTheory.Kernel.condKernel_apply_eq_condKernel`: the kernel `condKernel` is almost
  everywhere equal to the measure `condKernel`.
-/

public section

open MeasureTheory Set Filter MeasurableSpace

open scoped ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

section Measure

variable {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]

/-! ### Uniqueness of `Measure.condKernel`

The conditional kernel of a measure is unique almost everywhere. -/

/--
theorem `eq_condKernel_of_measure_eq_compProd'` / 定理 `eq_condKernel_of_measure_eq_compProd'`

English:
theorem eq_condKernel_of_measure_eq_compProd'
  statement: (κ : Kernel α Ω) [IsSFiniteKernel κ]
  proof: by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (Kernel.measurable_coe κ hs) (Kernel.measurable_coe ρ.condKernel hs) (fun t ht _ => ?_)
  conv_rhs => rw [Measure.setLIntegral_condKernel_eq_measure_prod ht hs, hκ]
  exact (Measure.compProd_apply_prod ht hs).symm

中文:
定理 eq_condKernel_of_measure_eq_compProd'
  结论: (κ : 核 α Ω) [是SFiniteKernel κ]
  证明: by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (Kernel.measurable_coe κ hs) (Kernel.measurable_coe ρ.condKernel hs) (fun t ht _ => ?_)
  conv_rhs => rw [Measure.setLIntegral_condKernel_eq_measure_prod ht hs, hκ]
  exact (Measure.compProd_apply_prod ht hs).symm

Depends on / 依赖: Kernel, Kernel.measurable_coe, Measure, Measure.compProd_apply_prod, Measure.setLIntegral_condKernel_eq_measure_prod, ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite, compProd_apply_prod, condKernel, conv_rhs, measurable_coe, setLIntegral_condKernel_eq_measure_prod
-/
theorem eq_condKernel_of_measure_eq_compProd' (κ : Kernel α Ω) [IsSFiniteKernel κ]
    (hκ : ρ = ρ.fst otimesₘ κ) {s : Set Ω} (hs : MeasurableSet s) :
    forallᵐ x ∂ρ.fst, κ x s = ρ.condKernel x s := by
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (Kernel.measurable_coe κ hs) (Kernel.measurable_coe ρ.condKernel hs) (fun t ht _ => ?_)
  conv_rhs => rw [Measure.setLIntegral_condKernel_eq_measure_prod ht hs, hκ]
  exact (Measure.compProd_apply_prod ht hs).symm

/--
lemma `eq_condKernel_of_measure_eq_compProd_real` / 引理 `eq_condKernel_of_measure_eq_compProd_real`

English:
lemma eq_condKernel_of_measure_eq_compProd_real
  statement: {ρ : Measure (α × Real)} [IsFiniteMeasure ρ]
  proof: by
  have huniv : forallᵐ x ∂ρ.fst, κ x Set.univ = ρ.condKernel x Set.univ :=
    eq_condKernel_of_measure_eq_compProd' κ hκ MeasurableSet.univ
  suffices forallᵐ x ∂ρ.fst, forall ⦃t⦄, MeasurableSet t -> κ x t = ρ.condKernel x t by
    filter_upwards [this] with x hx
    ext t ht; exact hx ht
  apply MeasurableSpace.ae_induction_on_inter Real.borel_eq_generateFrom_Iic_rat
    Real.isPiSystem_Iic_rat
  · simp
  · simp only [iUnion_singleton_eq_range, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact ae_all_iff.2 fun q => eq_condKernel_of_measure_eq_compProd' κ hκ measurableSet_Iic
  · filter_upwards [huniv] with x hxuniv t ht heq
    rw [measure_compl ht <| measure_ne_top _ _]; rw [heq]; rw [hxuniv]; rw [measure_compl ht <| measure_ne_top _ _]
  · refine ae_of_all _ (fun x f hdisj hf heq => ?_)
    rw [measure_iUnion hdisj hf]; rw [measure_iUnion hdisj hf]
    exact tsum_congr heq

中文:
引理 eq_condKernel_of_measure_eq_compProd_real
  结论: {ρ : 测度 (α × 实数)} [是有限测度 ρ]
  证明: by
  have huniv : forallᵐ x ∂ρ.fst, κ x Set.univ = ρ.condKernel x Set.univ :=
    eq_condKernel_of_measure_eq_compProd' κ hκ MeasurableSet.univ
  suffices forallᵐ x ∂ρ.fst, forall ⦃t⦄, MeasurableSet t -> κ x t = ρ.condKernel x t by
    filter_upwards [this] with x hx
    ext t ht; exact hx ht
  apply MeasurableSpace.ae_induction_on_inter Real.borel_eq_generateFrom_Iic_rat
    Real.isPiSystem_Iic_rat
  · simp
  · simp only [iUnion_singleton_eq_range, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact ae_all_iff.2 fun q => eq_condKernel_of_measure_eq_compProd' κ hκ measurableSet_Iic
  · filter_upwards [huniv] with x hxuniv t ht heq
    rw [measure_compl ht <| measure_ne_top _ _]; rw [heq]; rw [hxuniv]; rw [measure_compl ht <| measure_ne_top _ _]
  · refine ae_of_all _ (fun x f hdisj hf heq => ?_)
    rw [measure_iUnion hdisj hf]; rw [measure_iUnion hdisj hf]
    exact tsum_congr heq

Depends on / 依赖: MeasurableSet, MeasurableSet.univ, MeasurableSpace, MeasurableSpace.ae_induction_on_inter, Real.borel_eq_generateFrom_Iic_rat, Real.isPiSystem_Iic_rat, Set.univ, ae_all_if, ae_induction_on_inter, borel_eq_generateFrom_Iic_rat, condKernel, eq_condKernel_of_measure_eq_compProd, filter_upwards, forall_apply_eq_imp_iff, forall_exists_index, iUnion_singleton_eq_range, isPiSystem_Iic_rat, mem_range
-/
lemma eq_condKernel_of_measure_eq_compProd_real {ρ : Measure (α × Real)} [IsFiniteMeasure ρ]
    (κ : Kernel α Real) [IsFiniteKernel κ] (hκ : ρ = ρ.fst otimesₘ κ) :
    forallᵐ x ∂ρ.fst, κ x = ρ.condKernel x := by
  have huniv : forallᵐ x ∂ρ.fst, κ x Set.univ = ρ.condKernel x Set.univ :=
    eq_condKernel_of_measure_eq_compProd' κ hκ MeasurableSet.univ
  suffices forallᵐ x ∂ρ.fst, forall ⦃t⦄, MeasurableSet t -> κ x t = ρ.condKernel x t by
    filter_upwards [this] with x hx
    ext t ht; exact hx ht
  apply MeasurableSpace.ae_induction_on_inter Real.borel_eq_generateFrom_Iic_rat
    Real.isPiSystem_Iic_rat
  · simp
  · simp only [iUnion_singleton_eq_range, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    exact ae_all_iff.2 fun q => eq_condKernel_of_measure_eq_compProd' κ hκ measurableSet_Iic
  · filter_upwards [huniv] with x hxuniv t ht heq
    rw [measure_compl ht <| measure_ne_top _ _]; rw [heq]; rw [hxuniv]; rw [measure_compl ht <| measure_ne_top _ _]
  · refine ae_of_all _ (fun x f hdisj hf heq => ?_)
    rw [measure_iUnion hdisj hf]; rw [measure_iUnion hdisj hf]
    exact tsum_congr heq

/--
theorem `eq_condKernel_of_measure_eq_compProd` / 定理 `eq_condKernel_of_measure_eq_compProd`

English:
theorem eq_condKernel_of_measure_eq_compProd
  statement: (κ : Kernel α Ω) [IsFiniteKernel κ]
  proof: by
  -- The idea is to transport the question to `ℝ` from `Ω` using `embeddingReal`
  -- and then construct a measure on `α × ℝ`
  let f := embeddingReal Ω
  have hf := measurableEmbedding_embeddingReal Ω
  set ρ' : Measure (α × Real) := ρ.map (Prod.map id f) with hρ'def
  have hρ' : ρ'.fst = ρ.fst := by
    ext s hs
    rw [hρ'def]; rw [Measure.fst_apply]; rw [Measure.fst_apply]; rw [Measure.map_apply]
    exacts [rfl, Measurable.prod measurable_fst <| hf.measurable.comp measurable_snd,
      measurable_fst hs, hs, hs]
  have hρ'' : forallᵐ x ∂ρ.fst, Kernel.map κ f x = ρ'.condKernel x := by
    rw [← hρ']
    refine eq_condKernel_of_measure_eq_compProd_real (Kernel.map κ f) ?_
    ext s hs
    conv_lhs => rw [hρ'def, hκ]
    rw [Measure.map_apply (measurable_id.prodMap hf.measurable) hs]; rw [hρ']; rw [Measure.compProd_apply hs]; rw [Measure.compProd_apply (measurable_id.prodMap hf.measurable hs)]
    congr with a
    rw [Kernel.map_apply' _ hf.measurable]
    exacts [rfl, measurable_prodMk_left hs]
  suffices forallᵐ x ∂ρ.fst, forall s, MeasurableSet s -> ρ'.condKernel x s = ρ.condKernel x (f ⁻¹' s) by
    filter_upwards [hρ'', this] with x hx h
    rw [Kernel.map_apply _ hf.measurable] at hx
    ext s hs
    rw [← Set.preimage_image_eq s hf.injective]; rw [← Measure.map_apply hf.measurable hf.measurableSet_image.2 hs]; rw [hx]; rw [h _ hf.measurableSet_image.2 hs]
  suffices ρ.map (Prod.map id f) = (ρ.fst otimesₘ (Kernel.map ρ.condKernel f)) by
    rw [← hρ'] at this
    have heq := eq_condKernel_of_measure_eq_compProd_real _ this
    rw [hρ'] at heq
    filter_upwards [heq] with x hx s hs
    rw [← hx]; rw [Kernel.map_apply _ hf.measurable]; rw [Measure.map_apply hf.measurable hs]
  ext s hs
  conv_lhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [Measure.compProd_apply hs]; rw [Measure.map_apply (measurable_id.prodMap hf.measurable) hs]; rw [Measure.compProd_apply]
  · congr with a
    rw [Kernel.map_apply' _ hf.measurable]
    exacts [rfl, measurable_prodMk_left hs]
  · exact measurable_id.prodMap hf.measurable hs

中文:
定理 eq_condKernel_of_measure_eq_compProd
  结论: (κ : 核 α Ω) [是FiniteKernel κ]
  证明: by
  -- The idea is to transport the question to `ℝ` from `Ω` using `embeddingReal`
  -- and then construct a measure on `α × ℝ`
  let f := embeddingReal Ω
  have hf := measurableEmbedding_embeddingReal Ω
  set ρ' : Measure (α × Real) := ρ.map (Prod.map id f) with hρ'def
  have hρ' : ρ'.fst = ρ.fst := by
    ext s hs
    rw [hρ'def]; rw [Measure.fst_apply]; rw [Measure.fst_apply]; rw [Measure.map_apply]
    exacts [rfl, Measurable.prod measurable_fst <| hf.measurable.comp measurable_snd,
      measurable_fst hs, hs, hs]
  have hρ'' : forallᵐ x ∂ρ.fst, Kernel.map κ f x = ρ'.condKernel x := by
    rw [← hρ']
    refine eq_condKernel_of_measure_eq_compProd_real (Kernel.map κ f) ?_
    ext s hs
    conv_lhs => rw [hρ'def, hκ]
    rw [Measure.map_apply (measurable_id.prodMap hf.measurable) hs]; rw [hρ']; rw [Measure.compProd_apply hs]; rw [Measure.compProd_apply (measurable_id.prodMap hf.measurable hs)]
    congr with a
    rw [Kernel.map_apply' _ hf.measurable]
    exacts [rfl, measurable_prodMk_left hs]
  suffices forallᵐ x ∂ρ.fst, forall s, MeasurableSet s -> ρ'.condKernel x s = ρ.condKernel x (f ⁻¹' s) by
    filter_upwards [hρ'', this] with x hx h
    rw [Kernel.map_apply _ hf.measurable] at hx
    ext s hs
    rw [← Set.preimage_image_eq s hf.injective]; rw [← Measure.map_apply hf.measurable hf.measurableSet_image.2 hs]; rw [hx]; rw [h _ hf.measurableSet_image.2 hs]
  suffices ρ.map (Prod.map id f) = (ρ.fst otimesₘ (Kernel.map ρ.condKernel f)) by
    rw [← hρ'] at this
    have heq := eq_condKernel_of_measure_eq_compProd_real _ this
    rw [hρ'] at heq
    filter_upwards [heq] with x hx s hs
    rw [← hx]; rw [Kernel.map_apply _ hf.measurable]; rw [Measure.map_apply hf.measurable hs]
  ext s hs
  conv_lhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [Measure.compProd_apply hs]; rw [Measure.map_apply (measurable_id.prodMap hf.measurable) hs]; rw [Measure.compProd_apply]
  · congr with a
    rw [Kernel.map_apply' _ hf.measurable]
    exacts [rfl, measurable_prodMk_left hs]
  · exact measurable_id.prodMap hf.measurable hs
-/
theorem eq_condKernel_of_measure_eq_compProd (κ : Kernel α Ω) [IsFiniteKernel κ]
    (hκ : ρ = ρ.fst otimesₘ κ) :
    forallᵐ x ∂ρ.fst, κ x = ρ.condKernel x := by
  -- The idea is to transport the question to `ℝ` from `Ω` using `embeddingReal`
  -- and then construct a measure on `α × ℝ`
  let f := embeddingReal Ω
  have hf := measurableEmbedding_embeddingReal Ω
  set ρ' : Measure (α × Real) := ρ.map (Prod.map id f) with hρ'def
  have hρ' : ρ'.fst = ρ.fst := by
    ext s hs
    rw [hρ'def]; rw [Measure.fst_apply]; rw [Measure.fst_apply]; rw [Measure.map_apply]
    exacts [rfl, Measurable.prod measurable_fst <| hf.measurable.comp measurable_snd,
      measurable_fst hs, hs, hs]
  have hρ'' : forallᵐ x ∂ρ.fst, Kernel.map κ f x = ρ'.condKernel x := by
    rw [← hρ']
    refine eq_condKernel_of_measure_eq_compProd_real (Kernel.map κ f) ?_
    ext s hs
    conv_lhs => rw [hρ'def, hκ]
    rw [Measure.map_apply (measurable_id.prodMap hf.measurable) hs]; rw [hρ']; rw [Measure.compProd_apply hs]; rw [Measure.compProd_apply (measurable_id.prodMap hf.measurable hs)]
    congr with a
    rw [Kernel.map_apply' _ hf.measurable]
    exacts [rfl, measurable_prodMk_left hs]
  suffices forallᵐ x ∂ρ.fst, forall s, MeasurableSet s -> ρ'.condKernel x s = ρ.condKernel x (f ⁻¹' s) by
    filter_upwards [hρ'', this] with x hx h
    rw [Kernel.map_apply _ hf.measurable] at hx
    ext s hs
    rw [← Set.preimage_image_eq s hf.injective]; rw [← Measure.map_apply hf.measurable hf.measurableSet_image.2 hs]; rw [hx]; rw [h _ hf.measurableSet_image.2 hs]
  suffices ρ.map (Prod.map id f) = (ρ.fst otimesₘ (Kernel.map ρ.condKernel f)) by
    rw [← hρ'] at this
    have heq := eq_condKernel_of_measure_eq_compProd_real _ this
    rw [hρ'] at heq
    filter_upwards [heq] with x hx s hs
    rw [← hx]; rw [Kernel.map_apply _ hf.measurable]; rw [Measure.map_apply hf.measurable hs]
  ext s hs
  conv_lhs => rw [← ρ.disintegrate ρ.condKernel]
  rw [Measure.compProd_apply hs]; rw [Measure.map_apply (measurable_id.prodMap hf.measurable) hs]; rw [Measure.compProd_apply]
  · congr with a
    rw [Kernel.map_apply' _ hf.measurable]
    exacts [rfl, measurable_prodMk_left hs]
  · exact measurable_id.prodMap hf.measurable hs

/--
lemma `condKernel_compProd` / 引理 `condKernel_compProd`

English:
lemma condKernel_compProd
  given: (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α Ω) [IsMarkovKernel κ]
  proof: by
  suffices κ =ᵐ[(μ otimesₘ κ).fst] (μ otimesₘ κ).condKernel by symm; rwa [Measure.fst_compProd] at this
  refine eq_condKernel_of_measure_eq_compProd _ ?_
  rw [Measure.fst_compProd]

中文:
引理 condKernel_compProd
  条件: (μ : 测度 α) [是有限测度 μ] (κ : 核 α Ω) [是MarkovKernel κ]
  证明: by
  suffices κ =ᵐ[(μ otimesₘ κ).fst] (μ otimesₘ κ).condKernel by symm; rwa [Measure.fst_compProd] at this
  refine eq_condKernel_of_measure_eq_compProd _ ?_
  rw [Measure.fst_compProd]

Depends on / 依赖: Measure, Measure.fst_compProd, condKernel, eq_condKernel_of_measure_eq_compProd, fst_compProd
-/
lemma condKernel_compProd (μ : Measure α) [IsFiniteMeasure μ] (κ : Kernel α Ω) [IsMarkovKernel κ] :
    (μ otimesₘ κ).condKernel =ᵐ[μ] κ := by
  suffices κ =ᵐ[(μ otimesₘ κ).fst] (μ otimesₘ κ).condKernel by symm; rwa [Measure.fst_compProd] at this
  refine eq_condKernel_of_measure_eq_compProd _ ?_
  rw [Measure.fst_compProd]

end Measure

section KernelAndMeasure

/--
lemma `Kernel.apply_eq_measure_condKernel_of_compProd_eq` / 引理 `Kernel.apply_eq_measure_condKernel_of_compProd_eq`

English:
lemma Kernel.apply_eq_measure_condKernel_of_compProd_eq
  proof: by
  have : ρ a = (ρ a).fst otimesₘ Kernel.comap κ (fun b => (a, b)) measurable_prodMk_left := by
    ext s hs
    conv_lhs => rw [← hκ]
    rw [Measure.compProd_apply hs]; rw [Kernel.compProd_apply hs]
    rfl
  have h := eq_condKernel_of_measure_eq_compProd _ this
  rw [Kernel.fst_apply]
  filter_upwards [h] with b hb
  rw [← hb]; rw [Kernel.comap_apply]

中文:
引理 核.apply_eq_measure_condKernel_of_compProd_eq
  证明: by
  have : ρ a = (ρ a).fst otimesₘ Kernel.comap κ (fun b => (a, b)) measurable_prodMk_left := by
    ext s hs
    conv_lhs => rw [← hκ]
    rw [Measure.compProd_apply hs]; rw [Kernel.compProd_apply hs]
    rfl
  have h := eq_condKernel_of_measure_eq_compProd _ this
  rw [Kernel.fst_apply]
  filter_upwards [h] with b hb
  rw [← hb]; rw [Kernel.comap_apply]

Depends on / 依赖: Kernel, Kernel.comap, Kernel.comap_apply, Kernel.compProd_apply, Kernel.fst_apply, Measure, Measure.compProd_apply, comap_apply, compProd_apply, conv_lhs, eq_condKernel_of_measure_eq_compProd, filter_upwards, fst_apply, measurable_prodMk_left
-/
lemma Kernel.apply_eq_measure_condKernel_of_compProd_eq
    {ρ : Kernel α (β × Ω)} [IsFiniteKernel ρ] {κ : Kernel (α × β) Ω} [IsFiniteKernel κ]
    (hκ : Kernel.fst ρ otimesₖ κ = ρ) (a : α) :
    (fun b => κ (a, b)) =ᵐ[Kernel.fst ρ a] (ρ a).condKernel := by
  have : ρ a = (ρ a).fst otimesₘ Kernel.comap κ (fun b => (a, b)) measurable_prodMk_left := by
    ext s hs
    conv_lhs => rw [← hκ]
    rw [Measure.compProd_apply hs]; rw [Kernel.compProd_apply hs]
    rfl
  have h := eq_condKernel_of_measure_eq_compProd _ this
  rw [Kernel.fst_apply]
  filter_upwards [h] with b hb
  rw [← hb]; rw [Kernel.comap_apply]

/--
lemma `Kernel.condKernel_apply_eq_condKernel` / 引理 `Kernel.condKernel_apply_eq_condKernel`

English:
lemma Kernel.condKernel_apply_eq_condKernel
  statement: [CountableOrCountablyGenerated α β]
  proof: Kernel.apply_eq_measure_condKernel_of_compProd_eq (κ.disintegrate _) a

中文:
引理 核.condKernel_apply_eq_condKernel
  结论: [余untableOrCountablyGenerated α β]
  证明: Kernel.apply_eq_measure_condKernel_of_compProd_eq (κ.disintegrate _) a

Depends on / 依赖: Kernel, Kernel.apply_eq_measure_condKernel_of_compProd_eq, apply_eq_measure_condKernel_of_compProd_eq, disintegrate
-/
lemma Kernel.condKernel_apply_eq_condKernel [CountableOrCountablyGenerated α β]
    (κ : Kernel α (β × Ω)) [IsFiniteKernel κ] (a : α) :
    (fun b => Kernel.condKernel κ (a, b)) =ᵐ[Kernel.fst κ a] (κ a).condKernel :=
  Kernel.apply_eq_measure_condKernel_of_compProd_eq (κ.disintegrate _) a

/--
lemma `condKernel_const` / 引理 `condKernel_const`

English:
lemma condKernel_const
  statement: [CountableOrCountablyGenerated α β] (ρ : Measure (β × Ω)) [IsFiniteMeasure ρ]
  proof: by
  have h := Kernel.condKernel_apply_eq_condKernel (Kernel.const α ρ) a
  simp_rw [Kernel.fst_apply, Kernel.const_apply] at h
  filter_upwards [h] with b hb using hb

中文:
引理 condKernel_const
  结论: [余untableOrCountablyGenerated α β] (ρ : 测度 (β × Ω)) [是有限测度 ρ]
  证明: by
  have h := Kernel.condKernel_apply_eq_condKernel (Kernel.const α ρ) a
  simp_rw [Kernel.fst_apply, Kernel.const_apply] at h
  filter_upwards [h] with b hb using hb

Depends on / 依赖: Kernel, Kernel.condKernel_apply_eq_condKernel, Kernel.const, Kernel.const_apply, Kernel.fst_apply, condKernel_apply_eq_condKernel, const_apply, filter_upwards, fst_apply, simp_rw
-/
lemma condKernel_const [CountableOrCountablyGenerated α β] (ρ : Measure (β × Ω)) [IsFiniteMeasure ρ]
    (a : α) :
    (fun b => Kernel.condKernel (Kernel.const α ρ) (a, b)) =ᵐ[ρ.fst] ρ.condKernel := by
  have h := Kernel.condKernel_apply_eq_condKernel (Kernel.const α ρ) a
  simp_rw [Kernel.fst_apply, Kernel.const_apply] at h
  filter_upwards [h] with b hb using hb

end KernelAndMeasure

section Kernel

/-! ### Uniqueness of `Kernel.condKernel`

The conditional kernel is unique almost everywhere. -/

/--
theorem `eq_condKernel_of_kernel_eq_compProd` / 定理 `eq_condKernel_of_kernel_eq_compProd`

English:
theorem eq_condKernel_of_kernel_eq_compProd
  statement: [CountableOrCountablyGenerated α β]
  proof: by
  filter_upwards [Kernel.condKernel_apply_eq_condKernel ρ a,
    Kernel.apply_eq_measure_condKernel_of_compProd_eq hκ a] with a h1 h2
  rw [h1]; rw [h2]

中文:
定理 eq_condKernel_of_kernel_eq_compProd
  结论: [余untableOrCountablyGenerated α β]
  证明: by
  filter_upwards [Kernel.condKernel_apply_eq_condKernel ρ a,
    Kernel.apply_eq_measure_condKernel_of_compProd_eq hκ a] with a h1 h2
  rw [h1]; rw [h2]

Depends on / 依赖: Kernel, Kernel.apply_eq_measure_condKernel_of_compProd_eq, Kernel.condKernel_apply_eq_condKernel, apply_eq_measure_condKernel_of_compProd_eq, condKernel_apply_eq_condKernel, filter_upwards
-/
theorem eq_condKernel_of_kernel_eq_compProd [CountableOrCountablyGenerated α β]
    {ρ : Kernel α (β × Ω)} [IsFiniteKernel ρ] {κ : Kernel (α × β) Ω} [IsFiniteKernel κ]
    (hκ : Kernel.fst ρ otimesₖ κ = ρ) (a : α) :
    forallᵐ x ∂(Kernel.fst ρ a), κ (a, x) = Kernel.condKernel ρ (a, x) := by
  filter_upwards [Kernel.condKernel_apply_eq_condKernel ρ a,
    Kernel.apply_eq_measure_condKernel_of_compProd_eq hκ a] with a h1 h2
  rw [h1]; rw [h2]

end Kernel

end ProbabilityTheory
