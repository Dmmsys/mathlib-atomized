/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Semivariation

/-!
# Product of vector measures

Given two vector measures, we define their product `μ.prod ν B` as the vector measure assigning
to a measurable product `s × t` the mass `B (μ s) (ν t)`, if such a vector measure exists.
We show that it exists when either `μ` or `ν` has finite variation.

The API is modelled on the one for the product of positive measures.
-/

public section

open Filter Function MeasureTheory RCLike Set TopologicalSpace Topology
open scoped ENNReal NNReal Finset

variable {ι X Y E F G H I J : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup G] [NormedSpace Real G]
  [NormedAddCommGroup H] [NormedSpace Real H]
  [NormedAddCommGroup I] [NormedSpace Real I]
  [NormedAddCommGroup J] [NormedSpace Real J]
  {μ : VectorMeasure X E} {ν : VectorMeasure Y F} {B : E ->L[Real] F ->L[Real] G}

namespace MeasureTheory.VectorMeasure

/--
Definition of `HasProd` / `HasProd` 的定义

English:
class HasProd
  parameters: (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E ->L[Real] F ->L[Real] G)
  axioms and operations (1):
    - exists_prod : exists ρ : VectorMeasure (X × Y) G, forall (s : Set X) (t : Set Y), MeasurableSet s -> MeasurableSet t -> ρ (s ×ˢ t) = B (μ s) (ν t)

中文:
类 有积类型
  参数: (μ : 向量测度 X E) (ν : 向量测度 Y F) (B : E ->L[实数] F ->L[实数] G)
  公理与运算 (1 个):
    - exists_prod : 存在 ρ : 向量测度 (X × Y) G, 对任意 (s : 集合 X) (t : 集合 Y), 可测集 s -> 可测集 t -> ρ (s ×ˢ t) = B (μ s) (ν t)
-/
class HasProd (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E ->L[Real] F ->L[Real] G) : Prop where
  exists_prod : exists ρ : VectorMeasure (X × Y) G, forall (s : Set X) (t : Set Y),
    MeasurableSet s -> MeasurableSet t -> ρ (s ×ˢ t) = B (μ s) (ν t)

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E ->L[Real] F ->L[Real] G)
  body: open scoped Classical in if h : HasProd μ ν B then h.exists_prod.choose else 0

中文:
定义 乘积
  签名: (μ : 向量测度 X E) (ν : 向量测度 Y F) (B : E ->L[实数] F ->L[实数] G)
  定义体: open scoped Classical in if h : HasProd μ ν B then h.exists_prod.choose else 0

Depends on / 依赖: Classical, HasProd, exists_prod, h.exists_prod.choose, scoped
-/
noncomputable def prod (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E ->L[Real] F ->L[Real] G) :
    VectorMeasure (X × Y) G :=
  open scoped Classical in if h : HasProd μ ν B then h.exists_prod.choose else 0

/--
lemma `prod_eq_zero_of_not_hasProd` / 引理 `prod_eq_zero_of_not_hasProd`

English:
lemma prod_eq_zero_of_not_hasProd
  given: (h : ¬HasProd μ ν B)
  proof: by
  grind [HasProd, prod]

中文:
引理 prod_eq_zero_of_not_hasProd
  条件: (h : ¬有积类型 μ ν B)
  证明: by
  grind [HasProd, prod]

Depends on / 依赖: HasProd
-/
lemma prod_eq_zero_of_not_hasProd (h : ¬HasProd μ ν B) :
    μ.prod ν B = 0 := by
  grind [HasProd, prod]

/--
lemma `prod_apply` / 引理 `prod_apply`

English:
lemma prod_apply
  given: [h : HasProd μ ν B] {s : Set X} {t : Set Y}
  proof: by
  rcases eq_or_ne s ∅ with rfl | hs
  · simp
  rcases eq_or_ne t ∅ with rfl | ht
  · simp
  by_cases h's : MeasurableSet s; swap
  · simp only [h's, not_false_eq_true, not_measurable, _root_.map_zero, _root_.zero_apply]
    rw [not_measurable]
    simp [measurableSet_prod, hs, ht, h's]
  by_cases h't : MeasurableSet t; swap
  · simp only [h't, not_false_eq_true, not_measurable, _root_.map_zero]
    rw [not_measurable]
    simp [measurableSet_prod, hs, ht, h't]
  simpa [prod, h] using h.exists_prod.choose_spec s t h's h't

中文:
引理 prod_apply
  条件: [h : 有积类型 μ ν B] {s : 集合 X} {t : 集合 Y}
  证明: by
  rcases eq_or_ne s ∅ with rfl | hs
  · simp
  rcases eq_or_ne t ∅ with rfl | ht
  · simp
  by_cases h's : MeasurableSet s; swap
  · simp only [h's, not_false_eq_true, not_measurable, _root_.map_zero, _root_.zero_apply]
    rw [not_measurable]
    simp [measurableSet_prod, hs, ht, h's]
  by_cases h't : MeasurableSet t; swap
  · simp only [h't, not_false_eq_true, not_measurable, _root_.map_zero]
    rw [not_measurable]
    simp [measurableSet_prod, hs, ht, h't]
  simpa [prod, h] using h.exists_prod.choose_spec s t h's h't
-/
@[simp] lemma prod_apply [h : HasProd μ ν B] {s : Set X} {t : Set Y} :
    μ.prod ν B (s ×ˢ t) = B (μ s) (ν t) := by
  rcases eq_or_ne s ∅ with rfl | hs
  · simp
  rcases eq_or_ne t ∅ with rfl | ht
  · simp
  by_cases h's : MeasurableSet s; swap
  · simp only [h's, not_false_eq_true, not_measurable, _root_.map_zero, _root_.zero_apply]
    rw [not_measurable]
    simp [measurableSet_prod, hs, ht, h's]
  by_cases h't : MeasurableSet t; swap
  · simp only [h't, not_false_eq_true, not_measurable, _root_.map_zero]
    rw [not_measurable]
    simp [measurableSet_prod, hs, ht, h't]
  simpa [prod, h] using h.exists_prod.choose_spec s t h's h't

/--
lemma `HasProd.flip` / 引理 `HasProd.flip`

English:
lemma HasProd.flip
  given: [HasProd μ ν B]
  statement: HasProd ν μ B.flip where
  proof: by
    refine ⟨(μ.prod ν B).map Prod.swap, fun s t hs ht => ?_⟩
    rw [map_apply _ (by fun_prop) (hs.prod ht)]
    simp

中文:
引理 有积类型.flip
  条件: [有积类型 μ ν B]
  结论: 有积类型 ν μ B.flip where
  证明: by
    refine ⟨(μ.prod ν B).map Prod.swap, fun s t hs ht => ?_⟩
    rw [map_apply _ (by fun_prop) (hs.prod ht)]
    simp

Depends on / 依赖: Prod.swap, fun_prop, hs.prod, map_apply
-/
lemma HasProd.flip [HasProd μ ν B] : HasProd ν μ B.flip where
  exists_prod := by
    refine ⟨(μ.prod ν B).map Prod.swap, fun s t hs ht => ?_⟩
    rw [map_apply _ (by fun_prop) (hs.prod ht)]
    simp

/--
lemma `hasProd_flip_iff` / 引理 `hasProd_flip_iff`

English:
lemma hasProd_flip_iff
  statement: HasProd ν μ B.flip ↔ HasProd μ ν B
  proof: ⟨fun h => by simpa using HasProd.flip (μ := ν) (ν := μ) (B := B.flip), fun h => HasProd.flip⟩

omit [NormedSpace Real F] in

中文:
引理 hasProd_flip_iff
  结论: 有积类型 ν μ B.flip ↔ 有积类型 μ ν B
  证明: ⟨fun h => by simpa using HasProd.flip (μ := ν) (ν := μ) (B := B.flip), fun h => HasProd.flip⟩

omit [NormedSpace Real F] in

Depends on / 依赖: B.flip, HasProd, HasProd.flip
-/
lemma hasProd_flip_iff : HasProd ν μ B.flip ↔ HasProd μ ν B :=
  ⟨fun h => by simpa using HasProd.flip (μ := ν) (ν := μ) (B := B.flip), fun h => HasProd.flip⟩

omit [NormedSpace Real F] in
/--
theorem `stronglyMeasurable_vectorMeasure_prodMk_left` / 定理 `stronglyMeasurable_vectorMeasure_prodMk_left`

English:
theorem stronglyMeasurable_vectorMeasure_prodMk_left
  statement: {s : Set (X × Y)}
  proof: by
  induction s, hs
    using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp [stronglyMeasurable_const]
  | basic s hs =>
    obtain ⟨s, hs, t, -, rfl⟩ := hs
    classical
    simpa [mk_preimage_prod_right_eq_if, of_if] using stronglyMeasurable_const.indicator hs
  | compl s hs ihs =>
    simp_rw [preimage_compl, VectorMeasure.of_compl (measurable_prodMk_left hs)]
    exact stronglyMeasurable_const.sub ihs
  | iUnion f hfd hfm ihf =>
    have (a : X) : HasSum (fun i => ν (Prod.mk a ⁻¹' f i)) (ν (Prod.mk a ⁻¹' ⋃ i, f i)) := by
      rw [preimage_iUnion]
      apply hasSum_of_disjoint_iUnion
      exacts [fun i => measurable_prodMk_left (hfm i), hfd.mono fun _ _ => .preimage _]
    exact StronglyMeasurable.hasSum ihf this

omit [NormedSpace Real E] in

中文:
定理 stronglyMeasurable_vectorMeasure_prodMk_left
  结论: {s : 集合 (X × Y)}
  证明: by
  induction s, hs
    using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp [stronglyMeasurable_const]
  | basic s hs =>
    obtain ⟨s, hs, t, -, rfl⟩ := hs
    classical
    simpa [mk_preimage_prod_right_eq_if, of_if] using stronglyMeasurable_const.indicator hs
  | compl s hs ihs =>
    simp_rw [preimage_compl, VectorMeasure.of_compl (measurable_prodMk_left hs)]
    exact stronglyMeasurable_const.sub ihs
  | iUnion f hfd hfm ihf =>
    have (a : X) : HasSum (fun i => ν (Prod.mk a ⁻¹' f i)) (ν (Prod.mk a ⁻¹' ⋃ i, f i)) := by
      rw [preimage_iUnion]
      apply hasSum_of_disjoint_iUnion
      exacts [fun i => measurable_prodMk_left (hfm i), hfd.mono fun _ _ => .preimage _]
    exact StronglyMeasurable.hasSum ihf this

omit [NormedSpace Real E] in

Depends on / 依赖: HasSum, MeasurableSpace, MeasurableSpace.induction_on_inter, Prod.mk, VectorMeasure, VectorMeasure.of_compl, classical, generateFrom_prod, generateFrom_prod.symm, iUnion, indicator, induction_on_inter, isPiSystem_prod, measurable_prodMk_left, mk_preimage_prod_right_eq_if, of_compl, of_if, preimage_compl, simp_rw, stronglyMeasurable_const
-/
theorem stronglyMeasurable_vectorMeasure_prodMk_left {s : Set (X × Y)}
    (hs : MeasurableSet s) : StronglyMeasurable fun x => ν (Prod.mk x ⁻¹' s) := by
  induction s, hs
    using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp [stronglyMeasurable_const]
  | basic s hs =>
    obtain ⟨s, hs, t, -, rfl⟩ := hs
    classical
    simpa [mk_preimage_prod_right_eq_if, of_if] using stronglyMeasurable_const.indicator hs
  | compl s hs ihs =>
    simp_rw [preimage_compl, VectorMeasure.of_compl (measurable_prodMk_left hs)]
    exact stronglyMeasurable_const.sub ihs
  | iUnion f hfd hfm ihf =>
    have (a : X) : HasSum (fun i => ν (Prod.mk a ⁻¹' f i)) (ν (Prod.mk a ⁻¹' ⋃ i, f i)) := by
      rw [preimage_iUnion]
      apply hasSum_of_disjoint_iUnion
      exacts [fun i => measurable_prodMk_left (hfm i), hfd.mono fun _ _ => .preimage _]
    exact StronglyMeasurable.hasSum ihf this

omit [NormedSpace Real E] in
/--
theorem `integrable_vectorMeasure_prodMk_left` / 定理 `integrable_vectorMeasure_prodMk_left`

English:
theorem integrable_vectorMeasure_prodMk_left
  statement: [IsFiniteMeasure μ.variation]
  proof: by
  refine Integrable.of_bound (μ := μ.variation) ?_ ν.bound ?_
  · exact (stronglyMeasurable_vectorMeasure_prodMk_left hs).aestronglyMeasurable
  · exact Eventually.of_forall (fun x => norm_apply_le_bound)

中文:
定理 integrable_vectorMeasure_prodMk_left
  结论: [是有限测度 μ.variation]
  证明: by
  refine Integrable.of_bound (μ := μ.variation) ?_ ν.bound ?_
  · exact (stronglyMeasurable_vectorMeasure_prodMk_left hs).aestronglyMeasurable
  · exact Eventually.of_forall (fun x => norm_apply_le_bound)

Depends on / 依赖: Eventually, Eventually.of_forall, Integrable, Integrable.of_bound, aestronglyMeasurable, norm_apply_le_bound, of_bound, of_forall, stronglyMeasurable_vectorMeasure_prodMk_left, variation
-/
theorem integrable_vectorMeasure_prodMk_left [IsFiniteMeasure μ.variation]
    {s : Set (X × Y)} (hs : MeasurableSet s) :
    μ.Integrable fun x => ν (Prod.mk x ⁻¹' s) := by
  refine Integrable.of_bound (μ := μ.variation) ?_ ν.bound ?_
  · exact (stronglyMeasurable_vectorMeasure_prodMk_left hs).aestronglyMeasurable
  · exact Eventually.of_forall (fun x => norm_apply_le_bound)

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def prodOfIsFiniteMeasureLeft
  body: open scoped Classical in
    if MeasurableSet s then ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B.flip; μ] else 0
  empty' := by simp
  not_measurable' := by simp +contextual
  m_iUnion' f f_meas f_disj := by
    simp only [f_meas, ↓reduceIte, implies_true, MeasurableSet.iUnion, preimage_iUnion,
      HasSum, SummationFilter.unconditional_filter]
    have A (a : Finset Nat) : ∑ y in a, ∫ᵛ x, ν (Prod.mk x ⁻¹' f y) ∂[B.flip; μ]
        = ∫ᵛ x, ∑ y in a, ν (Prod.mk x ⁻¹' f y) ∂[B.flip; μ] := by
      rw [integral_finsetSum _ (fun i hi => integrable_vectorMeasure_prodMk_left (f_meas i))]
    simp_rw [A]
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun x => ν.bound)
    · apply Eventually.of_forall (fun a => ?_)
      apply StronglyMeasurable.aestronglyMeasurable
      apply Finset.stronglyMeasurable_fun_sum _ (fun i hi => ?_)
      apply stronglyMeasurable_vectorMeasure_prodMk_left (f_meas i)
    · filter_upwards with a
      filter_upwards with x
      rw [← VectorMeasure.of_biUnion_finset]
      · apply norm_apply_le_bound
      · exact fun i hi j hj hij => (f_disj hij).preimage _
      · exact fun i hi => measurable_prodMk_left (f_meas i)
    · apply integrable_const
    · filter_upwards with x
      apply hasSum_of_disjoint_iUnion
      · exact fun i => measurable_prodMk_left (f_meas i)
      · exact fun i j hij => (f_disj hij).preimage _

中文:
定义 noncomputable
  签名: def prodOfIsFiniteMeasureLeft
  定义体: open scoped Classical in
    if MeasurableSet s then ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B.flip; μ] else 0
  empty' := by simp
  not_measurable' := by simp +contextual
  m_iUnion' f f_meas f_disj := by
    simp only [f_meas, ↓reduceIte, implies_true, MeasurableSet.iUnion, preimage_iUnion,
      HasSum, SummationFilter.unconditional_filter]
    have A (a : Finset Nat) : ∑ y in a, ∫ᵛ x, ν (Prod.mk x ⁻¹' f y) ∂[B.flip; μ]
        = ∫ᵛ x, ∑ y in a, ν (Prod.mk x ⁻¹' f y) ∂[B.flip; μ] := by
      rw [integral_finsetSum _ (fun i hi => integrable_vectorMeasure_prodMk_left (f_meas i))]
    simp_rw [A]
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun x => ν.bound)
    · apply Eventually.of_forall (fun a => ?_)
      apply StronglyMeasurable.aestronglyMeasurable
      apply Finset.stronglyMeasurable_fun_sum _ (fun i hi => ?_)
      apply stronglyMeasurable_vectorMeasure_prodMk_left (f_meas i)
    · filter_upwards with a
      filter_upwards with x
      rw [← VectorMeasure.of_biUnion_finset]
      · apply norm_apply_le_bound
      · exact fun i hi j hj hij => (f_disj hij).preimage _
      · exact fun i hi => measurable_prodMk_left (f_meas i)
    · apply integrable_const
    · filter_upwards with x
      apply hasSum_of_disjoint_iUnion
      · exact fun i => measurable_prodMk_left (f_meas i)
      · exact fun i j hij => (f_disj hij).preimage _
-/
private noncomputable def prodOfIsFiniteMeasureLeft
    (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E ->L[Real] F ->L[Real] G)
    [IsFiniteMeasure μ.variation] :
    VectorMeasure (X × Y) G where
  measureOf' s := open scoped Classical in
    if MeasurableSet s then ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B.flip; μ] else 0
  empty' := by simp
  not_measurable' := by simp +contextual
  m_iUnion' f f_meas f_disj := by
    simp only [f_meas, ↓reduceIte, implies_true, MeasurableSet.iUnion, preimage_iUnion,
      HasSum, SummationFilter.unconditional_filter]
    have A (a : Finset Nat) : ∑ y in a, ∫ᵛ x, ν (Prod.mk x ⁻¹' f y) ∂[B.flip; μ]
        = ∫ᵛ x, ∑ y in a, ν (Prod.mk x ⁻¹' f y) ∂[B.flip; μ] := by
      rw [integral_finsetSum _ (fun i hi => integrable_vectorMeasure_prodMk_left (f_meas i))]
    simp_rw [A]
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun x => ν.bound)
    · apply Eventually.of_forall (fun a => ?_)
      apply StronglyMeasurable.aestronglyMeasurable
      apply Finset.stronglyMeasurable_fun_sum _ (fun i hi => ?_)
      apply stronglyMeasurable_vectorMeasure_prodMk_left (f_meas i)
    · filter_upwards with a
      filter_upwards with x
      rw [← VectorMeasure.of_biUnion_finset]
      · apply norm_apply_le_bound
      · exact fun i hi j hj hij => (f_disj hij).preimage _
      · exact fun i hi => measurable_prodMk_left (f_meas i)
    · apply integrable_const
    · filter_upwards with x
      apply hasSum_of_disjoint_iUnion
      · exact fun i => measurable_prodMk_left (f_meas i)
      · exact fun i j hij => (f_disj hij).preimage _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteSpace
  signature: G] [IsFiniteMeasure μ.variation] : HasProd μ ν B where
  body: by
    classical
    refine ⟨prodOfIsFiniteMeasureLeft μ ν B, fun s t hs ht => ?_⟩
    simp [prodOfIsFiniteMeasureLeft, hs.prod ht, ↓reduceIte, mk_preimage_prod_right_eq_if,
      of_if, integral_indicator hs, ContinuousLinearMap.flip_apply, hs, restrict_apply]

中文:
实例 [完备空间
  签名: G] [是有限测度 μ.variation] : 有积类型 μ ν B where
  定义体: by
    classical
    refine ⟨prodOfIsFiniteMeasureLeft μ ν B, fun s t hs ht => ?_⟩
    simp [prodOfIsFiniteMeasureLeft, hs.prod ht, ↓reduceIte, mk_preimage_prod_right_eq_if,
      of_if, integral_indicator hs, ContinuousLinearMap.flip_apply, hs, restrict_apply]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.flip_apply, classical, flip_apply, hs.prod, integral_indicator, mk_preimage_prod_right_eq_if, of_if, prodOfIsFiniteMeasureLeft, reduceIte, restrict_apply
-/
instance [CompleteSpace G] [IsFiniteMeasure μ.variation] : HasProd μ ν B where
  exists_prod := by
    classical
    refine ⟨prodOfIsFiniteMeasureLeft μ ν B, fun s t hs ht => ?_⟩
    simp [prodOfIsFiniteMeasureLeft, hs.prod ht, ↓reduceIte, mk_preimage_prod_right_eq_if,
      of_if, integral_indicator hs, ContinuousLinearMap.flip_apply, hs, restrict_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteSpace
  signature: G] [h
  body: hasProd_flip_iff.1 inferInstance

中文:
实例 [完备空间
  签名: G] [h
  定义体: hasProd_flip_iff.1 inferInstance

Depends on / 依赖: hasProd_flip_iff
-/
instance [CompleteSpace G] [h : IsFiniteMeasure ν.variation] : HasProd μ ν B :=
  hasProd_flip_iff.1 inferInstance

/--
lemma `prod_eq_of_forall_apply_prod` / 引理 `prod_eq_of_forall_apply_prod`

English:
lemma prod_eq_of_forall_apply_prod
  statement: {ρ : VectorMeasure (X × Y) G} (hρ : forall (s : Set X) (t : Set Y),
  proof: by
  have : HasProd μ ν B := ⟨ρ, hρ⟩
  apply ext_of_generateFrom _ _ generateFrom_prod.symm isPiSystem_prod
  · rw [← univ_prod_univ, hρ _ _ MeasurableSet.univ MeasurableSet.univ, prod_apply]
  · rintro - ⟨s, hs, t, ht, rfl⟩
    rw [prod_apply]; rw [hρ _ _ hs ht]

中文:
引理 prod_eq_of_对任意_apply_prod
  结论: {ρ : 向量测度 (X × Y) G} (hρ : 对任意 (s : 集合 X) (t : 集合 Y),
  证明: by
  have : HasProd μ ν B := ⟨ρ, hρ⟩
  apply ext_of_generateFrom _ _ generateFrom_prod.symm isPiSystem_prod
  · rw [← univ_prod_univ, hρ _ _ MeasurableSet.univ MeasurableSet.univ, prod_apply]
  · rintro - ⟨s, hs, t, ht, rfl⟩
    rw [prod_apply]; rw [hρ _ _ hs ht]

Depends on / 依赖: HasProd, MeasurableSet, MeasurableSet.univ, ext_of_generateFrom, generateFrom_prod, generateFrom_prod.symm, isPiSystem_prod, prod_apply, univ_prod_univ
-/
lemma prod_eq_of_forall_apply_prod {ρ : VectorMeasure (X × Y) G} (hρ : forall (s : Set X) (t : Set Y),
    MeasurableSet s -> MeasurableSet t -> ρ (s ×ˢ t) = B (μ s) (ν t)) :
    μ.prod ν B = ρ := by
  have : HasProd μ ν B := ⟨ρ, hρ⟩
  apply ext_of_generateFrom _ _ generateFrom_prod.symm isPiSystem_prod
  · rw [← univ_prod_univ, hρ _ _ MeasurableSet.univ MeasurableSet.univ, prod_apply]
  · rintro - ⟨s, hs, t, ht, rfl⟩
    rw [prod_apply]; rw [hρ _ _ hs ht]

/--
lemma `prod_apply_eq_integral` / 引理 `prod_apply_eq_integral`

English:
lemma prod_apply_eq_integral
  statement: [CompleteSpace G] [IsFiniteMeasure μ.variation]
  proof: by
  have : μ.prod ν B = prodOfIsFiniteMeasureLeft μ ν B := by
    classical
    apply prod_eq_of_forall_apply_prod (fun s t hs ht => ?_)
    simp [prodOfIsFiniteMeasureLeft, hs.prod ht, ↓reduceIte, mk_preimage_prod_right_eq_if,
      of_if, integral_indicator hs, ContinuousLinearMap.flip_apply, restrict_apply, hs]
  rw [this]
  simp [prodOfIsFiniteMeasureLeft, hs]

中文:
引理 prod_apply_eq_integral
  结论: [完备空间 G] [是有限测度 μ.variation]
  证明: by
  have : μ.prod ν B = prodOfIsFiniteMeasureLeft μ ν B := by
    classical
    apply prod_eq_of_forall_apply_prod (fun s t hs ht => ?_)
    simp [prodOfIsFiniteMeasureLeft, hs.prod ht, ↓reduceIte, mk_preimage_prod_right_eq_if,
      of_if, integral_indicator hs, ContinuousLinearMap.flip_apply, restrict_apply, hs]
  rw [this]
  simp [prodOfIsFiniteMeasureLeft, hs]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.flip_apply, classical, flip_apply, hs.prod, integral_indicator, mk_preimage_prod_right_eq_if, of_if, prodOfIsFiniteMeasureLeft, prod_eq_of_forall_apply_prod, reduceIte, restrict_apply
-/
lemma prod_apply_eq_integral [CompleteSpace G] [IsFiniteMeasure μ.variation]
    {s : Set (X × Y)} (hs : MeasurableSet s) :
    μ.prod ν B s = ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B.flip; μ] := by
  have : μ.prod ν B = prodOfIsFiniteMeasureLeft μ ν B := by
    classical
    apply prod_eq_of_forall_apply_prod (fun s t hs ht => ?_)
    simp [prodOfIsFiniteMeasureLeft, hs.prod ht, ↓reduceIte, mk_preimage_prod_right_eq_if,
      of_if, integral_indicator hs, ContinuousLinearMap.flip_apply, restrict_apply, hs]
  rw [this]
  simp [prodOfIsFiniteMeasureLeft, hs]

/--
lemma `prod_flip_apply_eq_integral` / 引理 `prod_flip_apply_eq_integral`

English:
lemma prod_flip_apply_eq_integral
  statement: [CompleteSpace G] [IsFiniteMeasure μ.variation]
  proof: by
  simp [prod_apply_eq_integral hs]

中文:
引理 prod_flip_apply_eq_integral
  结论: [完备空间 G] [是有限测度 μ.variation]
  证明: by
  simp [prod_apply_eq_integral hs]

Depends on / 依赖: prod_apply_eq_integral
-/
lemma prod_flip_apply_eq_integral [CompleteSpace G] [IsFiniteMeasure μ.variation]
    {B : F ->L[Real] E ->L[Real] G} {s : Set (X × Y)} (hs : MeasurableSet s) :
    μ.prod ν B.flip s = ∫ᵛ x, ν (Prod.mk x ⁻¹' s) ∂[B; μ] := by
  simp [prod_apply_eq_integral hs]

/--
lemma `variation_prod_le` / 引理 `variation_prod_le`

English:
lemma variation_prod_le
  given: [CompleteSpace G] [IsFiniteMeasure μ.variation] [SFinite ν.variation]
  proof: by
  apply variation_le_of_forall_enorm_le (fun s hs => ?_)
  rw [prod_apply_eq_integral hs]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.prod_apply hs]
  grw [enorm_integral_le_lintegral_enorm, ContinuousLinearMap.opENorm_flip,
    enorm_measure_le_variation]

中文:
引理 variation_prod_le
  条件: [完备空间 G] [是有限测度 μ.variation] [SFinite ν.variation]
  证明: by
  apply variation_le_of_forall_enorm_le (fun s hs => ?_)
  rw [prod_apply_eq_integral hs]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.prod_apply hs]
  grw [enorm_integral_le_lintegral_enorm, ContinuousLinearMap.opENorm_flip,
    enorm_measure_le_variation]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opENorm_flip, Measure, Measure.prod_apply, Measure.smul_apply, enorm_integral_le_lintegral_enorm, enorm_measure_le_variation, opENorm_flip, prod_apply, prod_apply_eq_integral, smul_apply, smul_eq_mul, variation_le_of_forall_enorm_le
-/
lemma variation_prod_le [CompleteSpace G] [IsFiniteMeasure μ.variation] [SFinite ν.variation] :
    (μ.prod ν B).variation <= ‖B‖ₑ • μ.variation.prod ν.variation := by
  apply variation_le_of_forall_enorm_le (fun s hs => ?_)
  rw [prod_apply_eq_integral hs]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.prod_apply hs]
  grw [enorm_integral_le_lintegral_enorm, ContinuousLinearMap.opENorm_flip,
    enorm_measure_le_variation]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteSpace
  signature: G] [IsFiniteMeasure μ.variation] [IsFiniteMeasure ν.variation] :
  body: by
  have : IsFiniteMeasure (‖B‖ₑ • μ.variation.prod ν.variation) := by
    simp only [enorm_eq_nnnorm, Measure.coe_nnreal_smul]
    infer_instance
  exact isFiniteMeasure_of_le _ variation_prod_le

中文:
实例 [完备空间
  签名: G] [是有限测度 μ.variation] [是有限测度 ν.variation] :
  定义体: by
  have : IsFiniteMeasure (‖B‖ₑ • μ.variation.prod ν.variation) := by
    simp only [enorm_eq_nnnorm, Measure.coe_nnreal_smul]
    infer_instance
  exact isFiniteMeasure_of_le _ variation_prod_le

Depends on / 依赖: IsFiniteMeasure, Measure, Measure.coe_nnreal_smul, coe_nnreal_smul, enorm_eq_nnnorm, infer_instance, isFiniteMeasure_of_le, variation, variation.prod, variation_prod_le
-/
instance [CompleteSpace G] [IsFiniteMeasure μ.variation] [IsFiniteMeasure ν.variation] :
    IsFiniteMeasure (μ.prod ν B).variation := by
  have : IsFiniteMeasure (‖B‖ₑ • μ.variation.prod ν.variation) := by
    simp only [enorm_eq_nnnorm, Measure.coe_nnreal_smul]
    infer_instance
  exact isFiniteMeasure_of_le _ variation_prod_le

end MeasureTheory.VectorMeasure
