/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Defs

/-!
# Properties of variation

We prove basic properties of `variation` for `μ : VectorMeasure X V` in `ENormedAddCommMonoid V` on
`MeasurableSpace X`. It is defined as the supremum over partitions `{Eᵢ}` of `E`, of the quantity
`∑ᵢ, ‖μ(Eᵢ)‖`. This definition allows one to define the integral against
such vector-valued measures.

## Main results

* `enorm_measure_le_variation`: `‖μ E‖ₑ ≤ variation μ E`.
* `variation_zero`: `(0 : VectorMeasure X V).variation = 0`.
* `variation_neg`: `(-μ).variation = μ.variation`.
* `absolutelyContinuous`: `μ ≪ᵥ μ.variation`.
* `ennrealVariation_eq_self`: if `μ : VectorMeasure X ℝ≥0∞` then `μ.ennrealVariation = μ`.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

public section

open Finset Set
open scoped ENNReal NNReal

namespace MeasureTheory.VectorMeasure

variable {X V : Type*} {mX : MeasurableSpace X}

/--
lemma `sum_finpartition` / 引理 `sum_finpartition`

English:
lemma sum_finpartition
  statement: [AddCommMonoid V] [TopologicalSpace V] [T2Space V]
  proof: by
  rw [← μ.of_biUnion_finset (P.pairwiseDisjoint_apply (fun _ _ => rfl) rfl) (fun p _ => p.prop)]; rw [← Finset.sup_set_eq_biUnion]; rw [P.sup_parts_apply (fun _ _ => rfl) rfl]

中文:
引理 sum_finpartition
  结论: [AddCommMonoid V] [TopologicalSpace V] [T2Space V]
  证明: by
  rw [← μ.of_biUnion_finset (P.pairwiseDisjoint_apply (fun _ _ => rfl) rfl) (fun p _ => p.prop)]; rw [← Finset.sup_set_eq_biUnion]; rw [P.sup_parts_apply (fun _ _ => rfl) rfl]

Depends on / 依赖: Finset, Finset.sup_set_eq_biUnion, P.pairwiseDisjoint_apply, P.sup_parts_apply, of_biUnion_finset, p.prop, pairwiseDisjoint_apply, sup_parts_apply, sup_set_eq_biUnion
-/
lemma sum_finpartition [AddCommMonoid V] [TopologicalSpace V] [T2Space V]
    (μ : VectorMeasure X V) {s : Set X} {hs : MeasurableSet s}
    (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) : ∑ p in P.parts, μ p.val = μ s := by
  rw [← μ.of_biUnion_finset (P.pairwiseDisjoint_apply (fun _ _ => rfl) rfl) (fun p _ => p.prop)]; rw [← Finset.sup_set_eq_biUnion]; rw [P.sup_parts_apply (fun _ _ => rfl) rfl]

section Basic

variable [TopologicalSpace V] [ENormedAddCommMonoid V] [T2Space V]
  {μ ν : VectorMeasure X V} {s : Set X}

/--
lemma `variation_apply` / 引理 `variation_apply`

English:
lemma variation_apply
  given: (μ : VectorMeasure X V) (s : Set X)
  proof: rfl

@[simp]

中文:
引理 variation_apply
  条件: (μ : VectorMeasure X V) (s : Set X)
  证明: rfl

@[simp]
-/
lemma variation_apply (μ : VectorMeasure X V) (s : Set X) :
    μ.variation s = preVariation (‖μ ·‖ₑ) (isSigmaSubadditiveSetFun_enorm μ) (by simp) s := rfl

@[simp]
/--
lemma `ennrealVariation_apply` / 引理 `ennrealVariation_apply`

English:
lemma ennrealVariation_apply
  given: (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
  proof: Measure.toENNRealVectorMeasure_apply_measurable hs

中文:
引理 ennrealVariation_apply
  条件: (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
  证明: Measure.toENNRealVectorMeasure_apply_measurable hs

Depends on / 依赖: Measure, Measure.toENNRealVectorMeasure_apply_measurable, toENNRealVectorMeasure_apply_measurable
-/
lemma ennrealVariation_apply (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) :
    μ.ennrealVariation s = μ.variation s := Measure.toENNRealVectorMeasure_apply_measurable hs

/--
lemma `le_variation` / 引理 `le_variation`

English:
lemma le_variation
  statement: (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
  proof: by
  classical
  set Q := Finpartition.ofPairwiseDisjoint P hP₂ with defQ
  set Q' := Q.ofSubset (filter_subset MeasurableSet Q.parts) rfl with defQ'
  have hQ' : forall t in Q'.parts, t subseteq s := by simp [Q', Q]; grind
  calc
    ∑ p in P, ‖μ p‖ₑ = ∑ p in Q.parts, ‖μ p‖ₑ :=
      (Finpartition.

中文:
引理 le_variation
  结论: (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
  证明: by
  classical
  set Q := Finpartition.ofPairwiseDisjoint P hP₂ with defQ
  set Q' := Q.ofSubset (filter_subset MeasurableSet Q.parts) rfl with defQ'
  have hQ' : forall t in Q'.parts, t subseteq s := by simp [Q', Q]; grind
  calc
    ∑ p in P, ‖μ p‖ₑ = ∑ p in Q.parts, ‖μ p‖ₑ :=
      (Finpartition.

Depends on / 依赖: Finpartition, Finpartition.ofPairwiseDisjoint, Finpartition.sum_ofPairwiseDisjoint_eq_sum, Finset, Finset.sup_le, MeasurableSet, Q.ofSubset, Q.parts, Q.sum_ofSubset_eq_sum, classical, extendOfLE, filter_subset, ofPairwiseDisjoint, ofSubset, subseteq, sum_le_sum_of_subset, sum_ofPairwiseDisjoint_eq_sum, sum_ofSubset_eq_sum, sup_le
-/
lemma le_variation (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s) {P : Finset (Set X)}
    (hP₁ : forall t in P, t subseteq s) (hP₂ : (P : Set (Set X)).PairwiseDisjoint id) :
    ∑ p in P, ‖μ p‖ₑ <= μ.variation s := by
  classical
  set Q := Finpartition.ofPairwiseDisjoint P hP₂ with defQ
  set Q' := Q.ofSubset (filter_subset MeasurableSet Q.parts) rfl with defQ'
  have hQ' : forall t in Q'.parts, t subseteq s := by simp [Q', Q]; grind
  calc
    ∑ p in P, ‖μ p‖ₑ = ∑ p in Q.parts, ‖μ p‖ₑ :=
      (Finpartition.sum_ofPairwiseDisjoint_eq_sum hP₂ (by simp)).symm
    _ = ∑ p in Q'.parts, ‖μ p‖ₑ := (Q.sum_ofSubset_eq_sum _ _ _ (by simp_all)).symm
    _ <= ∑ p in (Q'.extendOfLE (Finset.sup_le hQ')).parts, ‖μ p‖ₑ :=
      sum_le_sum_of_subset (Q'.parts_subset_extendOfLE (Finset.sup_le hQ'))
    _ <= μ.variation s := by
      simp only [variation_apply, preVariation_apply, ennrealToMeasure_apply hs,
        ennrealPreVariation_apply]
      apply preVariation.sum_le' (fun p => ‖μ p‖ₑ) hs
      intro p hp
      rcases Q'.mem_parts_or_eq_sdiff_of_mem_extendOfLE _ hp with h | rfl
      · simp_all
      simp only [sup_set_eq_biUnion, id_eq]
exact hs.diff .biUnion (Finset.countable_toSet _) (by simp)

/--
lemma `exists_lt_sum_of_lt_variation` / 引理 `exists_lt_sum_of_lt_variation`

English:
lemma exists_lt_sum_of_lt_variation
  statement: (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
  proof: by
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply]
    at ha ⊢
  obtain ⟨P, hP⟩ : exists P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
      a < ∑ p in P.parts, (fun x => ‖μ x‖ₑ) p :=
    preVariation.exists_Finpartition_sum_gt (‖μ ·‖ₑ) _ ha
  

中文:
引理 exists_lt_sum_of_lt_variation
  结论: (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
  证明: by
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply]
    at ha ⊢
  obtain ⟨P, hP⟩ : exists P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
      a < ∑ p in P.parts, (fun x => ‖μ x‖ₑ) p :=
    preVariation.exists_Finpartition_sum_gt (‖μ ·‖ₑ) _ ha
  

Depends on / 依赖: Embedding, Finpartition, Function, Function.Embedding.subtype, Function.Embedding.subtype_apply, MeasurableSet, P.parts, P.parts.map, Subtype, Subtype.exists, ennrealPreVariation_apply, ennrealToMeasure_apply, exists_Finpartition_sum_gt, exists_and_right, exists_eq_right, forall_exists_index, mem_map, preVariation, preVariation.exists_Finpartition_sum_gt, subtype
-/
lemma exists_lt_sum_of_lt_variation (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
    {a : Real>=0∞} (ha : a < μ.variation s) :
    exists (P : Finset (Set X)), (forall t in P, t subseteq s) ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧
      (forall t in P, MeasurableSet t) ∧ a < ∑ p in P, ‖μ p‖ₑ := by
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply]
    at ha ⊢
  obtain ⟨P, hP⟩ : exists P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
      a < ∑ p in P.parts, (fun x => ‖μ x‖ₑ) p :=
    preVariation.exists_Finpartition_sum_gt (‖μ ·‖ₑ) _ ha
  refine ⟨P.parts.map (Function.Embedding.subtype _), ?_, ?_, ?_, ?_⟩
  · simp only [mem_map, Function.Embedding.subtype_apply, Subtype.exists, exists_and_right,
      exists_eq_right, forall_exists_index]
    intro t ht h't
    exact P.le h't
  · intro i hi j hj hij
    simp only [coe_map, Function.Embedding.subtype_apply, Set.mem_image, SetLike.mem_coe,
      Subtype.exists, exists_and_right, exists_eq_right] at hi hj
    rcases hi with ⟨h'i, i_mem⟩
    rcases hj with ⟨h'j, j_mem⟩
    exact (disjoint_subtype_iff (fun _ _ hs ht => hs.inter ht) _).1
      (P.disjoint i_mem j_mem (by simpa using hij))
  · simp +contextual
  · rwa [Finset.sum_map]

/--
lemma `exists_variation_le_add'` / 引理 `exists_variation_le_add'`

English:
lemma exists_variation_le_add'
  statement: (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
  proof: by
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply]
    at hμ ⊢
  obtain ⟨P, hP⟩ : exists P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
      preVariationFun (fun x => ‖μ x‖ₑ) s <= ∑ p in P.parts, (fun x => ‖μ x‖ₑ) ↑p + ε :=
    preVariation.exi

中文:
引理 exists_variation_le_add'
  结论: (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
  证明: by
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply]
    at hμ ⊢
  obtain ⟨P, hP⟩ : exists P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
      preVariationFun (fun x => ‖μ x‖ₑ) s <= ∑ p in P.parts, (fun x => ‖μ x‖ₑ) ↑p + ε :=
    preVariation.exi

Depends on / 依赖: Embedding, Finpartition, Function, Function.Embedding.subtype, Function.Embedding.subtype_apply, MeasurableSet, P.parts, P.parts.map, Subtype, Subtype.exists, ennrealPreVariation_apply, ennrealToMeasure_apply, exists_Finpartition_sum_ge, exists_and_right, exists_eq_right, mem_map, preVariation, preVariation.exists_Finpartition_sum_ge, preVariationFun, subtype
-/
lemma exists_variation_le_add' (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
    {ε : Real>=0∞} (hε : 0 < ε) (hμ : μ.variation s != ∞) :
    exists (P : Finset (Set X)), (forall t in P, t subseteq s) ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧
      (forall t in P, MeasurableSet t) ∧ μ.variation s <= ∑ p in P, ‖μ p‖ₑ + ε := by
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply]
    at hμ ⊢
  obtain ⟨P, hP⟩ : exists P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
      preVariationFun (fun x => ‖μ x‖ₑ) s <= ∑ p in P.parts, (fun x => ‖μ x‖ₑ) ↑p + ε :=
    preVariation.exists_Finpartition_sum_ge' (‖μ ·‖ₑ) hs hε hμ
  refine ⟨P.parts.map (Function.Embedding.subtype _), ?_, ?_, ?_, ?_⟩
  · simp only [mem_map, Function.Embedding.subtype_apply, Subtype.exists, exists_and_right,
      exists_eq_right, forall_exists_index]
    intro t ht h't
    exact P.le h't
  · intro i hi j hj hij
    simp only [coe_map, Function.Embedding.subtype_apply, Set.mem_image, SetLike.mem_coe,
      Subtype.exists, exists_and_right, exists_eq_right] at hi hj
    rcases hi with ⟨h'i, i_mem⟩
    rcases hj with ⟨h'j, j_mem⟩
    exact (disjoint_subtype_iff (fun _ _ hs ht => hs.inter ht) _).1
      (P.disjoint i_mem j_mem (by simpa using hij))
  · simp +contextual
  · rwa [Finset.sum_map]

/--
lemma `exists_variation_le_add` / 引理 `exists_variation_le_add`

English:
lemma exists_variation_le_add
  statement: (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
  proof: exists_variation_le_add' μ hs (mod_cast hε) hμ

中文:
引理 exists_variation_le_add
  结论: (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
  证明: exists_variation_le_add' μ hs (mod_cast hε) hμ

Depends on / 依赖: exists_variation_le_add, mod_cast
-/
lemma exists_variation_le_add (μ : VectorMeasure X V) {s : Set X} (hs : MeasurableSet s)
    {ε : Real>=0} (hε : 0 < ε) (hμ : μ.variation s != ∞) :
    exists (P : Finset (Set X)), (forall t in P, t subseteq s) ∧ ((P : Set (Set X)).PairwiseDisjoint id) ∧
      (forall t in P, MeasurableSet t) ∧ μ.variation s <= ∑ p in P, ‖μ p‖ₑ + ε :=
  exists_variation_le_add' μ hs (mod_cast hε) hμ

/--
theorem `enorm_measure_le_variation` / 定理 `enorm_measure_le_variation`

English:
theorem enorm_measure_le_variation
  given: (μ : VectorMeasure X V) (E : Set X)
  proof: by
  by_cases hE : MeasurableSet E
  swap; · simp [hE]
  by_cases hE' : (⟨E, hE⟩ : Subtype MeasurableSet) = ⊥
  · simp_all
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hE, ennrealPreVariation_apply]
  calc
    ‖μ E‖ₑ = ∑ p in (Finpartition.indiscrete hE').parts, ‖μ p‖ₑ := by si

中文:
定理 enorm_measure_le_variation
  条件: (μ : VectorMeasure X V) (E : Set X)
  证明: by
  by_cases hE : MeasurableSet E
  swap; · simp [hE]
  by_cases hE' : (⟨E, hE⟩ : Subtype MeasurableSet) = ⊥
  · simp_all
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hE, ennrealPreVariation_apply]
  calc
    ‖μ E‖ₑ = ∑ p in (Finpartition.indiscrete hE').parts, ‖μ p‖ₑ := by si

Depends on / 依赖: Finpartition, Finpartition.indiscrete, MeasurableSet, Subtype, ennrealPreVariation_apply, ennrealToMeasure_apply, indiscrete, preVariation, preVariation.sum_le, preVariationFun, sum_le, variation_apply
-/
theorem enorm_measure_le_variation (μ : VectorMeasure X V) (E : Set X) :
    ‖μ E‖ₑ <= variation μ E := by
  by_cases hE : MeasurableSet E
  swap; · simp [hE]
  by_cases hE' : (⟨E, hE⟩ : Subtype MeasurableSet) = ⊥
  · simp_all
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hE, ennrealPreVariation_apply]
  calc
    ‖μ E‖ₑ = ∑ p in (Finpartition.indiscrete hE').parts, ‖μ p‖ₑ := by simp
    _ <= preVariationFun (‖μ ·‖ₑ) E := by apply preVariation.sum_le

@[simp]
/--
lemma `variation_zero` / 引理 `variation_zero`

English:
lemma variation_zero
  statement: (0 : VectorMeasure X V).variation = 0
  proof: by
  simp only [variation, zero_apply, enorm_zero]
  exact preVariation_zero

中文:
引理 variation_zero
  结论: (0 : VectorMeasure X V).variation = 0
  证明: by
  simp only [variation, zero_apply, enorm_zero]
  exact preVariation_zero

Depends on / 依赖: enorm_zero, preVariation_zero, variation, zero_apply
-/
lemma variation_zero : (0 : VectorMeasure X V).variation = 0 := by
  simp only [variation, zero_apply, enorm_zero]
  exact preVariation_zero

/--
lemma `absolutelyContinuous` / 引理 `absolutelyContinuous`

English:
lemma absolutelyContinuous
  given: (μ : VectorMeasure X V)
  statement: μ ≪ᵥ μ.ennrealVariation
  proof: by
  intro s hs
  by_cases hsm : MeasurableSet s
  · suffices ‖μ s‖ₑ <= 0 by simp_all
    grw [enorm_measure_le_variation, ← ennrealVariation_apply _ hsm, hs]
  · exact μ.not_measurable hsm

中文:
引理 absolutelyContinuous
  条件: (μ : VectorMeasure X V)
  结论: μ ≪ᵥ μ.ennrealVariation
  证明: by
  intro s hs
  by_cases hsm : MeasurableSet s
  · suffices ‖μ s‖ₑ <= 0 by simp_all
    grw [enorm_measure_le_variation, ← ennrealVariation_apply _ hsm, hs]
  · exact μ.not_measurable hsm

Depends on / 依赖: MeasurableSet, ennrealVariation_apply, enorm_measure_le_variation, not_measurable
-/
lemma absolutelyContinuous (μ : VectorMeasure X V) : μ ≪ᵥ μ.ennrealVariation := by
  intro s hs
  by_cases hsm : MeasurableSet s
  · suffices ‖μ s‖ₑ <= 0 by simp_all
    grw [enorm_measure_le_variation, ← ennrealVariation_apply _ hsm, hs]
  · exact μ.not_measurable hsm

/--
lemma `variation_apply_le_of_forall_enorm_le` / 引理 `variation_apply_le_of_forall_enorm_le`

English:
lemma variation_apply_le_of_forall_enorm_le
  statement: {m : Measure X} (hs : MeasurableSet s)
  proof: by
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply,
    preVariationFun, hs, dite_true, iSup_le_iff]
  intro i
  calc
    ∑ x in i.parts, ‖μ x‖ₑ <= ∑ x in i.parts, m x := Finset.sum_le_sum
        (fun s hs => h s s.property (i.le hs))
    _ = m (i.pa

中文:
引理 variation_apply_le_of_forall_enorm_le
  结论: {m : Measure X} (hs : MeasurableSet s)
  证明: by
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply,
    preVariationFun, hs, dite_true, iSup_le_iff]
  intro i
  calc
    ∑ x in i.parts, ‖μ x‖ₑ <= ∑ x in i.parts, m x := Finset.sum_le_sum
        (fun s hs => h s s.property (i.le hs))
    _ = m (i.pa

Depends on / 依赖: Finset, Finset.sum_le_sum, MeasureTheory, MeasureTheory.measure_biUnion_finset, Subtype, Subtype.ext_iff, Subtype.val, b.property, disjoint, disjoint_iff, dite_true, ennrealPreVariation_apply, ennrealToMeasure_apply, ext_iff, i.disjoint, i.le, i.parts, i.parts.sup, iSup_le_iff, measure_biUnion_finset
-/
lemma variation_apply_le_of_forall_enorm_le {m : Measure X} (hs : MeasurableSet s)
    (h : forall E, MeasurableSet E -> E subseteq s -> ‖μ E‖ₑ <= m E) :
    μ.variation s <= m s := by
  simp only [variation_apply, preVariation, ennrealToMeasure_apply hs, ennrealPreVariation_apply,
    preVariationFun, hs, dite_true, iSup_le_iff]
  intro i
  calc
    ∑ x in i.parts, ‖μ x‖ₑ <= ∑ x in i.parts, m x := Finset.sum_le_sum
        (fun s hs => h s s.property (i.le hs))
    _ = m (i.parts.sup Subtype.val) := by
      rw [sup_set_eq_biUnion]
      refine (MeasureTheory.measure_biUnion_finset ?_ fun b _ => b.property).symm
      intro a ha b hb hab
      simpa [disjoint_iff, Subtype.ext_iff] using i.disjoint ha hb hab
    _ <= m s := by
      rw [sup_set_eq_biUnion]
exact measure_mono Set.iUnion₂_subset fun _ hp => Subtype.coe_le_coe.mpr (i.le hp)

/--
lemma `variation_le_of_forall_enorm_le` / 引理 `variation_le_of_forall_enorm_le`

English:
lemma variation_le_of_forall_enorm_le
  given: {m : Measure X} (h : forall E, MeasurableSet E -> ‖μ E‖ₑ <= m E)
  proof: Measure.le_intro fun _ hs _ => variation_apply_le_of_forall_enorm_le hs (fun E hE _ => h E hE)

中文:
引理 variation_le_of_forall_enorm_le
  条件: {m : Measure X} (h : 对任意 E, MeasurableSet E -> ‖μ E‖ₑ <= m E)
  证明: Measure.le_intro fun _ hs _ => variation_apply_le_of_forall_enorm_le hs (fun E hE _ => h E hE)

Depends on / 依赖: Measure, Measure.le_intro, le_intro, variation_apply_le_of_forall_enorm_le
-/
lemma variation_le_of_forall_enorm_le {m : Measure X} (h : forall E, MeasurableSet E -> ‖μ E‖ₑ <= m E) :
    μ.variation <= m :=
  Measure.le_intro fun _ hs _ => variation_apply_le_of_forall_enorm_le hs (fun E hE _ => h E hE)

/--
lemma `variation_add_le` / 引理 `variation_add_le`

English:
lemma variation_add_le
  given: [ContinuousAdd V]
  statement: variation (μ + ν) <= variation μ + variation ν
  proof: by
  refine variation_le_of_forall_enorm_le fun E _ => ?_
  calc
    _ <= ‖μ E‖ₑ + ‖ν E‖ₑ := enorm_add_le _ _
    _ <= μ.variation E + ν.variation E := by
      gcongr <;> exact enorm_measure_le_variation _ E

中文:
引理 variation_add_le
  条件: [ContinuousAdd V]
  结论: variation (μ + ν) <= variation μ + variation ν
  证明: by
  refine variation_le_of_forall_enorm_le fun E _ => ?_
  calc
    _ <= ‖μ E‖ₑ + ‖ν E‖ₑ := enorm_add_le _ _
    _ <= μ.variation E + ν.variation E := by
      gcongr <;> exact enorm_measure_le_variation _ E

Depends on / 依赖: enorm_add_le, enorm_measure_le_variation, variation, variation_le_of_forall_enorm_le
-/
lemma variation_add_le [ContinuousAdd V] : variation (μ + ν) <= variation μ + variation ν := by
  refine variation_le_of_forall_enorm_le fun E _ => ?_
  calc
    _ <= ‖μ E‖ₑ + ‖ν E‖ₑ := enorm_add_le _ _
    _ <= μ.variation E + ν.variation E := by
      gcongr <;> exact enorm_measure_le_variation _ E

/--
lemma `variation_finsetSum_le` / 引理 `variation_finsetSum_le`

English:
lemma variation_finsetSum_le
  given: [ContinuousAdd V] {ι} (s : Finset ι) (μ : ι -> VectorMeasure X V)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    simpa [Finset.sum_insert his] using
      variation_add_le.trans (add_le_add_right ih ((μ i).variation))

中文:
引理 variation_finsetSum_le
  条件: [ContinuousAdd V] {ι} (s : Finset ι) (μ : ι -> VectorMeasure X V)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    simpa [Finset.sum_insert his] using
      variation_add_le.trans (add_le_add_right ih ((μ i).variation))

Depends on / 依赖: Finset, Finset.induction_on, Finset.sum_insert, add_le_add_right, classical, induction_on, insert, sum_insert, variation, variation_add_le, variation_add_le.trans
-/
lemma variation_finsetSum_le [ContinuousAdd V] {ι} (s : Finset ι) (μ : ι -> VectorMeasure X V) :
    (∑ i in s, μ i).variation <= ∑ i in s, (μ i).variation := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    simpa [Finset.sum_insert his] using
      variation_add_le.trans (add_le_add_right ih ((μ i).variation))

/--
lemma `variation_apply_eq_zero` / 引理 `variation_apply_eq_zero`

English:
lemma variation_apply_eq_zero
  given: (hs : MeasurableSet s)
  proof: by
  refine ⟨fun h t hts ht => ?_, fun h => ?_⟩
  · rw [← enorm_eq_zero, ← le_zero_iff, ← h]
    apply (enorm_measure_le_variation _ _).trans (measure_mono hts)
  · suffices μ.variation s <= (0 : Measure X) s by simpa
    apply variation_apply_le_of_forall_enorm_le hs (fun t ht hts => ?_)
    simp [

中文:
引理 variation_apply_eq_zero
  条件: (hs : MeasurableSet s)
  证明: by
  refine ⟨fun h t hts ht => ?_, fun h => ?_⟩
  · rw [← enorm_eq_zero, ← le_zero_iff, ← h]
    apply (enorm_measure_le_variation _ _).trans (measure_mono hts)
  · suffices μ.variation s <= (0 : Measure X) s by simpa
    apply variation_apply_le_of_forall_enorm_le hs (fun t ht hts => ?_)
    simp [

Depends on / 依赖: Measure, enorm_eq_zero, enorm_measure_le_variation, le_zero_iff, measure_mono, variation, variation_apply_le_of_forall_enorm_le
-/
lemma variation_apply_eq_zero (hs : MeasurableSet s) :
    μ.variation s = 0 ↔ forall t, t subseteq s -> MeasurableSet t -> μ t = 0 := by
  refine ⟨fun h t hts ht => ?_, fun h => ?_⟩
  · rw [← enorm_eq_zero, ← le_zero_iff, ← h]
    apply (enorm_measure_le_variation _ _).trans (measure_mono hts)
  · suffices μ.variation s <= (0 : Measure X) s by simpa
    apply variation_apply_le_of_forall_enorm_le hs (fun t ht hts => ?_)
    simp [h t hts ht]

/--
lemma `variation_eq_zero` / 引理 `variation_eq_zero`

English:
lemma variation_eq_zero
  proof: by
    ext s hs
    apply enorm_eq_zero.1
    apply le_antisymm ?_ (by simp)
    grw [enorm_measure_le_variation]
    simp [h]
  mpr h := by simp [h]

中文:
引理 variation_eq_zero
  证明: by
    ext s hs
    apply enorm_eq_zero.1
    apply le_antisymm ?_ (by simp)
    grw [enorm_measure_le_variation]
    simp [h]
  mpr h := by simp [h]
-/
@[simp] lemma variation_eq_zero :
    μ.variation = 0 ↔ μ = 0 where
  mp h := by
    ext s hs
    apply enorm_eq_zero.1
    apply le_antisymm ?_ (by simp)
    grw [enorm_measure_le_variation]
    simp [h]
  mpr h := by simp [h]

/--
lemma `variation_restrict` / 引理 `variation_restrict`

English:
lemma variation_restrict
  given: (hs : MeasurableSet s)
  proof: by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun t ht => ?_)
    simp only [ht, Measure.restrict_apply, VectorMeasure.restrict_apply, hs]
    apply enorm_measure_le_variation
  · apply Measure.le_iff.2 (fun t ht => ?_)
    simp only [ht, Measure.restrict_apply]
    calc μ.variat

中文:
引理 variation_restrict
  条件: (hs : MeasurableSet s)
  证明: by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun t ht => ?_)
    simp only [ht, Measure.restrict_apply, VectorMeasure.restrict_apply, hs]
    apply enorm_measure_le_variation
  · apply Measure.le_iff.2 (fun t ht => ?_)
    simp only [ht, Measure.restrict_apply]
    calc μ.variat

Depends on / 依赖: Measure, Measure.le_iff, Measure.restrict_apply, VectorMeasure, VectorMeasure.restrict_apply, VectorMeasure.restrict_eq_self, enorm_measure_le_variation, ht.inter, le_antisymm, le_iff, restrict, restrict_apply, restrict_eq_self, u_meas, variation, variation_apply_le_of_forall_enorm_le, variation_le_of_forall_enorm_le
-/
lemma variation_restrict (hs : MeasurableSet s) :
    (μ.restrict s).variation = μ.variation.restrict s := by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun t ht => ?_)
    simp only [ht, Measure.restrict_apply, VectorMeasure.restrict_apply, hs]
    apply enorm_measure_le_variation
  · apply Measure.le_iff.2 (fun t ht => ?_)
    simp only [ht, Measure.restrict_apply]
    calc μ.variation (t inter s)
    _ <= (μ.restrict s).variation (t inter s) := by
      apply variation_apply_le_of_forall_enorm_le (ht.inter hs) (fun u u_meas hu => ?_)
      have : μ u = μ.restrict s u :=
        (VectorMeasure.restrict_eq_self _ hs u_meas (hu.trans inter_subset_right)).symm
      rw [this]
      apply enorm_measure_le_variation
    _ <= (μ.restrict s).variation t := by
      gcongr
      exact Set.inter_subset_left

/--
lemma `variation_restrict_le` / 引理 `variation_restrict_le`

English:
lemma variation_restrict_le
  statement: (μ.restrict s).variation <= μ.variation.restrict s
  proof: by
  by_cases hs : MeasurableSet s
  · simp [variation_restrict hs]
  · simp [restrict_not_measurable _ hs, Measure.zero_le]

中文:
引理 variation_restrict_le
  结论: (μ.restrict s).variation <= μ.variation.restrict s
  证明: by
  by_cases hs : MeasurableSet s
  · simp [variation_restrict hs]
  · simp [restrict_not_measurable _ hs, Measure.zero_le]

Depends on / 依赖: MeasurableSet, Measure, Measure.zero_le, restrict_not_measurable, variation_restrict, zero_le
-/
lemma variation_restrict_le : (μ.restrict s).variation <= μ.variation.restrict s := by
  by_cases hs : MeasurableSet s
  · simp [variation_restrict hs]
  · simp [restrict_not_measurable _ hs, Measure.zero_le]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiniteMeasure
  signature: μ.variation] : IsFiniteMeasure (μ.restrict s).variation
  body: isFiniteMeasure_of_le _ variation_restrict_le

中文:
实例 [IsFiniteMeasure
  签名: μ.variation] : IsFiniteMeasure (μ.restrict s).variation
  定义体: isFiniteMeasure_of_le _ variation_restrict_le

Depends on / 依赖: isFiniteMeasure_of_le, variation_restrict_le
-/
instance [IsFiniteMeasure μ.variation] : IsFiniteMeasure (μ.restrict s).variation :=
  isFiniteMeasure_of_le _ variation_restrict_le

variable {Y : Type*} [MeasurableSpace Y] {φ : X -> Y}

/--
lemma `variation_map_le` / 引理 `variation_map_le`

English:
lemma variation_map_le
  statement: (μ.map φ).variation <= μ.variation.map φ
  proof: by
  by_cases hφ : Measurable φ; swap
  · simp [VectorMeasure.map, hφ, Measure.zero_le]
  apply variation_le_of_forall_enorm_le (fun s hs => ?_)
  simp [VectorMeasure.map_apply _ hφ hs, Measure.map_apply hφ hs, enorm_measure_le_variation]

中文:
引理 variation_map_le
  结论: (μ.map φ).variation <= μ.variation.map φ
  证明: by
  by_cases hφ : Measurable φ; swap
  · simp [VectorMeasure.map, hφ, Measure.zero_le]
  apply variation_le_of_forall_enorm_le (fun s hs => ?_)
  simp [VectorMeasure.map_apply _ hφ hs, Measure.map_apply hφ hs, enorm_measure_le_variation]

Depends on / 依赖: Measurable, Measure, Measure.map_apply, Measure.zero_le, VectorMeasure, VectorMeasure.map, VectorMeasure.map_apply, enorm_measure_le_variation, map_apply, variation_le_of_forall_enorm_le, zero_le
-/
lemma variation_map_le : (μ.map φ).variation <= μ.variation.map φ := by
  by_cases hφ : Measurable φ; swap
  · simp [VectorMeasure.map, hφ, Measure.zero_le]
  apply variation_le_of_forall_enorm_le (fun s hs => ?_)
  simp [VectorMeasure.map_apply _ hφ hs, Measure.map_apply hφ hs, enorm_measure_le_variation]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsFiniteMeasure
  signature: μ.variation] : IsFiniteMeasure (μ.map φ).variation
  body: isFiniteMeasure_of_le _ variation_map_le

中文:
实例 [IsFiniteMeasure
  签名: μ.variation] : IsFiniteMeasure (μ.map φ).variation
  定义体: isFiniteMeasure_of_le _ variation_map_le

Depends on / 依赖: isFiniteMeasure_of_le, variation_map_le
-/
instance [IsFiniteMeasure μ.variation] : IsFiniteMeasure (μ.map φ).variation :=
  isFiniteMeasure_of_le _ variation_map_le

/--
theorem `_root_.MeasurableEmbedding.variation_map` / 定理 `_root_.MeasurableEmbedding.variation_map`

English:
theorem _root_.MeasurableEmbedding.variation_map
  given: (hφ : MeasurableEmbedding φ)
  proof: by
  apply le_antisymm variation_map_le ?_
  apply Measure.le_iff.2 (fun s hs => ?_)
  simp only [hφ.measurable, hs, Measure.map_apply]
  have : (μ.map φ).variation s = (μ.map φ).variation (s inter range φ) := by
    nth_rw 1 [← inter_union_sdiff s (range φ)]
    have : (μ.map φ).variation (s \ rang

中文:
定理 _root_.MeasurableEmbedding.variation_map
  条件: (hφ : MeasurableEmbedding φ)
  证明: by
  apply le_antisymm variation_map_le ?_
  apply Measure.le_iff.2 (fun s hs => ?_)
  simp only [hφ.measurable, hs, Measure.map_apply]
  have : (μ.map φ).variation s = (μ.map φ).variation (s inter range φ) := by
    nth_rw 1 [← inter_union_sdiff s (range φ)]
    have : (μ.map φ).variation (s \ rang

Depends on / 依赖: Measure, Measure.le_iff, Measure.map_apply, hs.diff, inter_union_sdiff, le_antisymm, le_iff, map_apply, measurable, measurableSet_range, measure_union, nth_rw, t_meas, variation, variation_apply_eq_zero, variation_map_le
-/
theorem _root_.MeasurableEmbedding.variation_map (hφ : MeasurableEmbedding φ) :
    (μ.map φ).variation = μ.variation.map φ := by
  apply le_antisymm variation_map_le ?_
  apply Measure.le_iff.2 (fun s hs => ?_)
  simp only [hφ.measurable, hs, Measure.map_apply]
  have : (μ.map φ).variation s = (μ.map φ).variation (s inter range φ) := by
    nth_rw 1 [← inter_union_sdiff s (range φ)]
    have : (μ.map φ).variation (s \ range φ) = 0 := by
      apply (variation_apply_eq_zero (hs.diff hφ.measurableSet_range)).2 (fun t ht t_meas => ?_)
      have : φ ⁻¹' t = ∅ := by grind
      simp [map_apply, t_meas, hφ.measurable, this]
    rw [measure_union (by grind) (hs.diff hφ.measurableSet_range)]; rw [this]; rw [add_zero]
  rw [this]; rw [← hφ.comap_preimage]
  apply variation_le_of_forall_enorm_le (fun t ht => ?_)
  simp only [hφ.comap_apply]
  apply le_trans ?_ (enorm_measure_le_variation _ _)
  rw [map_apply _ hφ.measurable (hφ.measurableSet_image.2 ht)]; rw [preimage_image_eq _ hφ.injective]

/--
lemma `variation_dirac` / 引理 `variation_dirac`

English:
lemma variation_dirac
  given: {x : X} {v : V}
  proof: by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun s hs => ?_)
    by_cases hx : x in s <;> simp [hs, hx]
  · apply Measure.le_iff.2 (fun s hs => ?_)
    apply le_trans ?_ (enorm_measure_le_variation _ _)
    by_cases hx : x in s <;> simp [hs, hx]

中文:
引理 variation_dirac
  条件: {x : X} {v : V}
  证明: by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun s hs => ?_)
    by_cases hx : x in s <;> simp [hs, hx]
  · apply Measure.le_iff.2 (fun s hs => ?_)
    apply le_trans ?_ (enorm_measure_le_variation _ _)
    by_cases hx : x in s <;> simp [hs, hx]
-/
@[simp] lemma variation_dirac {x : X} {v : V} :
    (VectorMeasure.dirac x v).variation = ‖v‖ₑ • Measure.dirac x := by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun s hs => ?_)
    by_cases hx : x in s <;> simp [hs, hx]
  · apply Measure.le_iff.2 (fun s hs => ?_)
    apply le_trans ?_ (enorm_measure_le_variation _ _)
    by_cases hx : x in s <;> simp [hs, hx]

end Basic

section NormedAddCommGroup

variable [NormedAddCommGroup V] {μ ν : VectorMeasure X V}

/--
theorem `norm_measure_le_variation` / 定理 `norm_measure_le_variation`

English:
theorem norm_measure_le_variation
  given: {E : Set X} (hE : μ.variation E != ∞ := by finiteness)
  proof: by
  rw [measureReal_def]; rw [← toReal_enorm]; rw [ENNReal.toReal_le_toReal (enorm_ne_top) hE]
  exact enorm_measure_le_variation μ E

中文:
定理 norm_measure_le_variation
  条件: {E : Set X} (hE : μ.variation E != ∞ := by finiteness)
  证明: by
  rw [measureReal_def]; rw [← toReal_enorm]; rw [ENNReal.toReal_le_toReal (enorm_ne_top) hE]
  exact enorm_measure_le_variation μ E

Depends on / 依赖: ENNReal, ENNReal.toReal_le_toReal, enorm_measure_le_variation, enorm_ne_top, finiteness, measureReal_def, toReal_enorm, toReal_le_toReal, variation, variation.real
-/
theorem norm_measure_le_variation {E : Set X} (hE : μ.variation E != ∞ := by finiteness) :
    ‖μ E‖ <= μ.variation.real E := by
  rw [measureReal_def]; rw [← toReal_enorm]; rw [ENNReal.toReal_le_toReal (enorm_ne_top) hE]
  exact enorm_measure_le_variation μ E

variable (μ) in
@[simp]
/--
lemma `variation_neg` / 引理 `variation_neg`

English:
lemma variation_neg
  statement: (-μ).variation = μ.variation
  proof: by simp [variation]

中文:
引理 variation_neg
  结论: (-μ).variation = μ.variation
  证明: by simp [variation]

Depends on / 依赖: variation
-/
lemma variation_neg : (-μ).variation = μ.variation := by simp [variation]

/--
lemma `variation_sub_le` / 引理 `variation_sub_le`

English:
lemma variation_sub_le
  statement: (μ - ν).variation <= μ.variation + ν.variation
  proof: by
  grw [sub_eq_add_neg, variation_add_le, variation_neg]

中文:
引理 variation_sub_le
  结论: (μ - ν).variation <= μ.variation + ν.variation
  证明: by
  grw [sub_eq_add_neg, variation_add_le, variation_neg]

Depends on / 依赖: sub_eq_add_neg, variation_add_le, variation_neg
-/
lemma variation_sub_le : (μ - ν).variation <= μ.variation + ν.variation := by
  grw [sub_eq_add_neg, variation_add_le, variation_neg]

/--
lemma `variation_smul_le` / 引理 `variation_smul_le`

English:
lemma variation_smul_le
  given: {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜}
  proof: by
  apply variation_le_of_forall_enorm_le (fun s hs => ?_)
  simp only [smul_apply, enorm_smul, Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  grw [enorm_measure_le_variation, enorm_eq_nnnorm]

中文:
引理 variation_smul_le
  条件: {𝕜 : 类型} [NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜}
  证明: by
  apply variation_le_of_forall_enorm_le (fun s hs => ?_)
  simp only [smul_apply, enorm_smul, Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  grw [enorm_measure_le_variation, enorm_eq_nnnorm]
-/
private lemma variation_smul_le {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜} :
    (c • μ).variation <= ‖c‖₊ • μ.variation := by
  apply variation_le_of_forall_enorm_le (fun s hs => ?_)
  simp only [smul_apply, enorm_smul, Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  grw [enorm_measure_le_variation, enorm_eq_nnnorm]

/--
lemma `variation_smul` / 引理 `variation_smul`

English:
lemma variation_smul
  given: {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜}
  proof: by
  apply le_antisymm variation_smul_le ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  calc ‖c‖₊ • μ.variation
  _ = ‖c‖₊ • (c⁻¹ • (c • μ)).variation := by simp [smul_smul, inv_mul_cancel₀ hc]
  _ <= ‖c‖₊ • ‖c⁻¹‖₊ • (c • μ).variation := by
    gcongr
    exact variation_smul_le
  _ = (c • μ).var

中文:
引理 variation_smul
  条件: {𝕜 : 类型} [NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜}
  证明: by
  apply le_antisymm variation_smul_le ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  calc ‖c‖₊ • μ.variation
  _ = ‖c‖₊ • (c⁻¹ • (c • μ)).variation := by simp [smul_smul, inv_mul_cancel₀ hc]
  _ <= ‖c‖₊ • ‖c⁻¹‖₊ • (c • μ).variation := by
    gcongr
    exact variation_smul_le
  _ = (c • μ).var

Depends on / 依赖: eq_or_ne, le_antisymm, nnnorm_ne_zero_iff, nnnorm_ne_zero_iff.mpr, smul_smul, variation, variation_smul_le
-/
lemma variation_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜} :
    (c • μ).variation = ‖c‖₊ • μ.variation := by
  apply le_antisymm variation_smul_le ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  calc ‖c‖₊ • μ.variation
  _ = ‖c‖₊ • (c⁻¹ • (c • μ)).variation := by simp [smul_smul, inv_mul_cancel₀ hc]
  _ <= ‖c‖₊ • ‖c⁻¹‖₊ • (c • μ).variation := by
    gcongr
    exact variation_smul_le
  _ = (c • μ).variation := by
    simp [smul_smul, mul_inv_cancel₀ (nnnorm_ne_zero_iff.mpr hc)]

instance {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜} [IsFiniteMeasure μ.variation] :
    IsFiniteMeasure (c • μ).variation := by
  simp only [variation_smul]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: X] : IsFiniteMeasure μ.variation where
  body: by
    classical
    let : Fintype X := Fintype.ofFinite X
    simp only [variation_apply, preVariation_apply, MeasurableSet.univ, ennrealToMeasure_apply,
      ennrealPreVariation_apply, preVariationFun, ↓reduceDIte, ← sup_univ_eq_ciSup]
    exact (Finset.sup_lt_iff (by simp)).2 (fun b hb => by sim

中文:
实例 [Finite
  签名: X] : IsFiniteMeasure μ.variation where
  定义体: by
    classical
    let : Fintype X := Fintype.ofFinite X
    simp only [variation_apply, preVariation_apply, MeasurableSet.univ, ennrealToMeasure_apply,
      ennrealPreVariation_apply, preVariationFun, ↓reduceDIte, ← sup_univ_eq_ciSup]
    exact (Finset.sup_lt_iff (by simp)).2 (fun b hb => by sim

Depends on / 依赖: ENNReal, ENNReal.sum_lt_top, Finset, Finset.sup_lt_iff, Fintype, Fintype.ofFinite, MeasurableSet, MeasurableSet.univ, classical, ennrealPreVariation_apply, ennrealToMeasure_apply, enorm_lt_top, ofFinite, preVariationFun, preVariation_apply, reduceDIte, sum_lt_top, sup_lt_iff, sup_univ_eq_ciSup, variation_apply
-/
instance [Finite X] : IsFiniteMeasure μ.variation where
  measure_univ_lt_top := by
    classical
    let : Fintype X := Fintype.ofFinite X
    simp only [variation_apply, preVariation_apply, MeasurableSet.univ, ennrealToMeasure_apply,
      ennrealPreVariation_apply, preVariationFun, ↓reduceDIte, ← sup_univ_eq_ciSup]
    exact (Finset.sup_lt_iff (by simp)).2 (fun b hb => by simp [ENNReal.sum_lt_top, enorm_lt_top])

instance {x : X} {v : V} : IsFiniteMeasure (VectorMeasure.dirac x v).variation := by
  simp only [variation_dirac, enorm_eq_nnnorm, Measure.coe_nnreal_smul]
  infer_instance

/--
lemma `_root_.MeasureTheory.Measure.variation_toSignedMeasure` / 引理 `_root_.MeasureTheory.Measure.variation_toSignedMeasure`

English:
lemma _root_.MeasureTheory.Measure.variation_toSignedMeasure
  proof: by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun s hs => ?_)
    simp [hs, Measure.real, Real.enorm_eq_ofReal]
  · apply Measure.le_iff.2 (fun s hs => ?_)
    apply le_trans ?_ (enorm_measure_le_variation _ _)
    simp [hs, Measure.real, Real.enorm_eq_ofReal]

中文:
引理 _root_.MeasureTheory.Measure.variation_toSignedMeasure
  证明: by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun s hs => ?_)
    simp [hs, Measure.real, Real.enorm_eq_ofReal]
  · apply Measure.le_iff.2 (fun s hs => ?_)
    apply le_trans ?_ (enorm_measure_le_variation _ _)
    simp [hs, Measure.real, Real.enorm_eq_ofReal]
-/
@[simp] lemma _root_.MeasureTheory.Measure.variation_toSignedMeasure
    {μ : Measure X} [IsFiniteMeasure μ] :
    μ.toSignedMeasure.variation = μ := by
  apply le_antisymm
  · apply variation_le_of_forall_enorm_le (fun s hs => ?_)
    simp [hs, Measure.real, Real.enorm_eq_ofReal]
  · apply Measure.le_iff.2 (fun s hs => ?_)
    apply le_trans ?_ (enorm_measure_le_variation _ _)
    simp [hs, Measure.real, Real.enorm_eq_ofReal]

/--
lemma `_root_.MeasureTheory.SignedMeasure.exists_subset_lt_enorm_apply_of_lt_variation` / 引理 `_root_.MeasureTheory.SignedMeasure.exists_subset_lt_enorm_apply_of_lt_variation`

English:
lemma _root_.MeasureTheory.SignedMeasure.exists_subset_lt_enorm_apply_of_lt_variation
  proof: by
  /- One may almost realize the variation through a partition into finitely many sets.
  As their measures are real numbers, we can group together those of positive measure, and
  also those of negative measure. This gives two measurable sets. Among these two, the one with the
  largest measure i

中文:
引理 _root_.MeasureTheory.SignedMeasure.exists_subset_lt_enorm_apply_of_lt_variation
  证明: by
  /- One may almost realize the variation through a partition into finitely many sets.
  As their measures are real numbers, we can group together those of positive measure, and
  also those of negative measure. This gives two measurable sets. Among these two, the one with the
  largest measure i
-/
lemma _root_.MeasureTheory.SignedMeasure.exists_subset_lt_enorm_apply_of_lt_variation
    (μ : SignedMeasure X) {s : Set X} (hs : MeasurableSet s)
    {a : Real>=0∞} (ha : a < μ.variation s) :
    exists t subseteq s, MeasurableSet t ∧ a < 2 * ‖μ t‖ₑ := by
  /- One may almost realize the variation through a partition into finitely many sets.
  As their measures are real numbers, we can group together those of positive measure, and
  also those of negative measure. This gives two measurable sets. Among these two, the one with the
  largest measure in absolute value satisfies the result. -/
  obtain ⟨P, Ps, P_disj, P_meas, hP⟩ : exists (P : Finset (Set X)), (forall t in P, t subseteq s) ∧
    ((P : Set (Set X)).PairwiseDisjoint id) ∧
    (forall t in P, MeasurableSet t) ∧ a < ∑ p in P, ‖μ p‖ₑ := exists_lt_sum_of_lt_variation _ hs ha
  have I : (∑ p in P.filter (fun p => 0 <= μ p), ‖μ p‖ₑ) =
      ‖μ (⋃ p in P.filter (fun p => 0 <= μ p), p)‖ₑ := by
    simp only [Real.norm_eq_abs, enorm_eq_nnnorm,
      ← ENNReal.ofNNReal_finsetSum, ENNReal.coe_inj, ← NNReal.coe_inj,
      NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs]
    have A : ∑ x in P with 0 <= μ x, |μ x| = μ (⋃ x in P.filter (fun x => 0 <= μ x), x) := calc
      _ = ∑ x in P with 0 <= μ x, μ x := by
        apply Finset.sum_congr rfl (fun p hp => ?_)
        simp only [Finset.mem_filter] at hp
        simp [hp]
      _ = μ (⋃ x in P.filter (fun x => 0 <= μ x), x) := by
        rw [of_biUnion_finset]
        · apply P_disj.subset (by grind)
        · grind
    rw [A]; rw [abs_of_nonneg]
    rw [← A]
    exact Finset.sum_nonneg (fun p hp => by positivity)
  have J : (∑ p in P.filter (fun p => ¬ 0 <= μ p), ‖μ p‖ₑ) =
      ‖μ (⋃ p in P.filter (fun p => ¬ 0 <= μ p), p)‖ₑ := by
    simp only [not_le, enorm_eq_nnnorm, ← ENNReal.ofNNReal_finsetSum,
      ENNReal.coe_inj, ← NNReal.coe_inj, NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs]
    have A : ∑ x in P with μ x < 0, |μ x| = - μ (⋃ x in P.filter (fun x => μ x < 0), x) := calc
      ∑ x in P with μ x < 0, |μ x|
      _ = ∑ x in P with μ x < 0, -μ x := by
        refine Finset.sum_congr rfl (fun p hp => ?_)
        simp only [Finset.mem_filter] at hp
        simp [hp.2.le]
      _ = -μ (⋃ x in P.filter (fun x => μ x < 0), x) := by
        rw [of_biUnion_finset]
        · simp
        · apply P_disj.subset (by grind)
        · grind
    rw [A]; rw [abs_of_nonpos]
    rw [← neg_nonneg]; rw [← A]
    exact Finset.sum_nonneg (fun p hp => by positivity)
  simp_rw [two_mul]
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p => 0 <= μ p)]; rw [I]; rw [J] at hP
  rcases le_total (‖μ (⋃ p in P.filter (fun p => ¬ 0 <= μ p), p)‖ₑ)
    (‖μ (⋃ p in P.filter (fun p => 0 <= μ p), p)‖ₑ) with h | h
  · refine ⟨⋃ p in P.filter (fun p => 0 <= μ p), p, ?_, ?_, ?_⟩
    · simp; grind
    · exact Finset.measurableSet_biUnion _ (by grind)
    · exact hP.trans_le (by gcongr)
  · refine ⟨⋃ p in P.filter (fun p => ¬ 0 <= μ p), p, ?_, ?_, ?_⟩
    · simp; grind
    · exact Finset.measurableSet_biUnion _ (by grind)
    · exact hP.trans_le (by gcongr)

end NormedAddCommGroup

section ENNReal

variable (μ : VectorMeasure X Real>=0∞)

/-- For `μ : VectorMeasure X ℝ≥0∞` and measurable `s`, the supremum over Finpartitions of
`⟨s, hs⟩ : Subtype MeasurableSet` of the sum of `μ` over parts equals `μ s`. -/
@[simp]
/--
lemma `iSup_sum_finpartition_parts` / 引理 `iSup_sum_finpartition_parts`

English:
lemma iSup_sum_finpartition_parts
  given: {s : Set X} (hs : MeasurableSet s)
  proof: by
  simp_rw [μ.sum_finpartition, iSup_const]

中文:
引理 iSup_sum_finpartition_parts
  条件: {s : Set X} (hs : MeasurableSet s)
  证明: by
  simp_rw [μ.sum_finpartition, iSup_const]

Depends on / 依赖: iSup_const, simp_rw, sum_finpartition
-/
lemma iSup_sum_finpartition_parts {s : Set X} (hs : MeasurableSet s) :
    ⨆ (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)), ∑ p in P.parts, μ p.val = μ s := by
  simp_rw [μ.sum_finpartition, iSup_const]

/--
lemma `preVariationFun_apply_of_ennreal` / 引理 `preVariationFun_apply_of_ennreal`

English:
lemma preVariationFun_apply_of_ennreal
  given: (s : Set X)
  statement: preVariationFun μ s = μ s
  proof: by
  by_cases h : MeasurableSet s
  · rw [preVariationFun_apply]
    exact iSup_sum_finpartition_parts μ h
  · rw [preVariationFun_of_not_measurableSet μ h, not_measurable μ h]

中文:
引理 preVariationFun_apply_of_ennreal
  条件: (s : Set X)
  结论: preVariationFun μ s = μ s
  证明: by
  by_cases h : MeasurableSet s
  · rw [preVariationFun_apply]
    exact iSup_sum_finpartition_parts μ h
  · rw [preVariationFun_of_not_measurableSet μ h, not_measurable μ h]

Depends on / 依赖: MeasurableSet, iSup_sum_finpartition_parts, not_measurable, preVariationFun_apply, preVariationFun_of_not_measurableSet
-/
lemma preVariationFun_apply_of_ennreal (s : Set X) : preVariationFun μ s = μ s := by
  by_cases h : MeasurableSet s
  · rw [preVariationFun_apply]
    exact iSup_sum_finpartition_parts μ h
  · rw [preVariationFun_of_not_measurableSet μ h, not_measurable μ h]

/--
theorem `variation_eq_ennrealToMeasure` / 定理 `variation_eq_ennrealToMeasure`

English:
theorem variation_eq_ennrealToMeasure
  statement: μ.variation = μ.ennrealToMeasure
  proof: by
  ext _ hs
  simp [preVariationFun_apply_of_ennreal, variation_apply, preVariation_apply,
    ennrealPreVariation_apply, ennrealToMeasure_apply hs]

@[simp]

中文:
定理 variation_eq_ennrealToMeasure
  结论: μ.variation = μ.ennrealToMeasure
  证明: by
  ext _ hs
  simp [preVariationFun_apply_of_ennreal, variation_apply, preVariation_apply,
    ennrealPreVariation_apply, ennrealToMeasure_apply hs]

@[simp]

Depends on / 依赖: ennrealPreVariation_apply, ennrealToMeasure_apply, preVariationFun_apply_of_ennreal, preVariation_apply, variation_apply
-/
theorem variation_eq_ennrealToMeasure : μ.variation = μ.ennrealToMeasure := by
  ext _ hs
  simp [preVariationFun_apply_of_ennreal, variation_apply, preVariation_apply,
    ennrealPreVariation_apply, ennrealToMeasure_apply hs]

@[simp]
/--
theorem `ennrealVariation_eq_self` / 定理 `ennrealVariation_eq_self`

English:
theorem ennrealVariation_eq_self
  statement: μ.ennrealVariation = μ
  proof: by
  simp [variation_eq_ennrealToMeasure, ennrealVariation]

中文:
定理 ennrealVariation_eq_self
  结论: μ.ennrealVariation = μ
  证明: by
  simp [variation_eq_ennrealToMeasure, ennrealVariation]

Depends on / 依赖: ennrealVariation, variation_eq_ennrealToMeasure
-/
theorem ennrealVariation_eq_self : μ.ennrealVariation = μ := by
  simp [variation_eq_ennrealToMeasure, ennrealVariation]

end ENNReal

end MeasureTheory.VectorMeasure
