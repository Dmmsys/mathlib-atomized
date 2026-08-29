/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.Operations
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Outer measures from functions

Given an arbitrary function `m : Set α → ℝ≥0∞` that sends `∅` to `0` we can define an outer
measure on `α` that on `s` is defined to be the infimum of `∑ᵢ, m (sᵢ)` for all collections of sets
`sᵢ` that cover `s`. This is the unique maximal outer measure that is at most the given function.

Given an outer measure `m`, the Carathéodory-measurable sets are the sets `s` such that
for all sets `t` we have `m t = m (t ∩ s) + m (t \ s)`. This forms a measurable space.

## Main definitions and statements

* `OuterMeasure.boundedBy` is the greatest outer measure that is at most the given function.
  If you know that the given function sends `∅` to `0`, then `OuterMeasure.ofFunction` is a
  special case.
* `sInf_eq_boundedBy_sInfGen` is a characterization of the infimum of outer measures.

## References

* <https://en.wikipedia.org/wiki/Outer_measure>
* <https://en.wikipedia.org/wiki/Carath%C3%A9odory%27s_criterion>

## Tags

outer measure, Carathéodory-measurable, Carathéodory's criterion

-/

@[expose] public section

assert_not_exists Module.Basis

noncomputable section

open Set Function Filter
open scoped NNReal Topology ENNReal

namespace MeasureTheory
namespace OuterMeasure

section OfFunction

variable {α : Type*}

/--
Definition of `ofFunction` / `ofFunction` 的定义

English:
definition ofFunction
  signature: (m : Set α -> Real>=0∞) (m_empty : m ∅ = 0)
  body: let μ s := ⨅ (f : Nat -> Set α) (_ : s subseteq ⋃ i, f i), ∑' i, m (f i)
  { measureOf := μ
    empty := by
      rw [← nonpos_iff_eq_zero]
exact (iInf_le_of_le fun _ => ∅) iInf_le_of_le (empty_subset _) by simpa
    mono := fun {_ _} hs => iInf_mono fun _ => iInf_mono' fun hb => ⟨hs.trans hb, le_rf

中文:
定义 ofFunction
  签名: (m : Set α -> 实数>=0∞) (m_empty : m ∅ = 0)
  定义体: let μ s := ⨅ (f : Nat -> Set α) (_ : s subseteq ⋃ i, f i), ∑' i, m (f i)
  { measureOf := μ
    empty := by
      rw [← nonpos_iff_eq_zero]
exact (iInf_le_of_le fun _ => ∅) iInf_le_of_le (empty_subset _) by simpa
    mono := fun {_ _} hs => iInf_mono fun _ => iInf_mono' fun hb => ⟨hs.trans hb, le_rf
-/
protected def ofFunction (m : Set α -> Real>=0∞) (m_empty : m ∅ = 0) : OuterMeasure α :=
  let μ s := ⨅ (f : Nat -> Set α) (_ : s subseteq ⋃ i, f i), ∑' i, m (f i)
  { measureOf := μ
    empty := by
      rw [← nonpos_iff_eq_zero]
exact (iInf_le_of_le fun _ => ∅) iInf_le_of_le (empty_subset _) by simpa
    mono := fun {_ _} hs => iInf_mono fun _ => iInf_mono' fun hb => ⟨hs.trans hb, le_rfl⟩
    iUnion_nat := fun s _ =>
ENNReal.le_of_forall_pos_le_add by
        intro ε hε (hb : (∑' i, μ (s i)) < ∞)
        rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 hε).ne' Nat with ⟨ε', hε', hl⟩
        grw [← hl]
        rw [← ENNReal.tsum_add]
        choose f hf using
          show forall i, exists f : Nat -> Set α, (s i subseteq ⋃ i, f i) ∧ (∑' i, m (f i)) < μ (s i) + ε' i by
            intro i
            have : μ (s i) < μ (s i) + ε' i :=
              ENNReal.lt_add_right (ne_top_of_le_ne_top hb.ne <| ENNReal.le_tsum _)
                (by simpa using (hε' i).ne')
            rcases iInf_lt_iff.mp this with ⟨t, ht⟩
            exists t
            contrapose! ht
            exact le_iInf ht
        refine le_trans ?_ (ENNReal.tsum_le_tsum fun i => le_of_lt (hf i).2)
        rw [← ENNReal.tsum_prod]; rw [← Nat.pairEquiv.symm.tsum_eq]
        refine iInf_le_of_le _ (iInf_le _ ?_)
        apply iUnion_subset
        intro i
        apply Subset.trans (hf i).1
        apply iUnion_subset
        simp only [Nat.pairEquiv_symm_apply]
        rw [iUnion_unpair]
        intro j
        apply subset_iUnion₂ i }

variable (m : Set α -> Real>=0∞) (m_empty : m ∅ = 0)

/--
theorem `ofFunction_apply` / 定理 `ofFunction_apply`

English:
theorem ofFunction_apply
  given: (s : Set α)
  proof: rfl

中文:
定理 ofFunction_apply
  条件: (s : Set α)
  证明: rfl
-/
theorem ofFunction_apply (s : Set α) :
    OuterMeasure.ofFunction m m_empty s = ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t), ∑' n, m (t n) :=
  rfl

/--
theorem `ofFunction_eq_iInf_mem` / 定理 `ofFunction_eq_iInf_mem`

English:
theorem ofFunction_eq_iInf_mem
  given: {P : Set α -> Prop} (m_top : forall s, ¬ P s -> m s = ∞) (s : Set α)
  proof: by
  rw [OuterMeasure.ofFunction_apply]
  apply le_antisymm
  · exact le_iInf fun t => le_iInf fun _ => le_iInf fun h => iInf₂_le _ (by exact h)
  · simp_rw [le_iInf_iff]
    refine fun t ht_subset => iInf_le_of_le t ?_
    by_cases ht : forall i, P (t i)
    · exact iInf_le_of_le ht (iInf_le_of_le 

中文:
定理 ofFunction_eq_iInf_mem
  条件: {P : Set α -> 命题} (m_top : 对任意 s, ¬ P s -> m s = ∞) (s : Set α)
  证明: by
  rw [OuterMeasure.ofFunction_apply]
  apply le_antisymm
  · exact le_iInf fun t => le_iInf fun _ => le_iInf fun h => iInf₂_le _ (by exact h)
  · simp_rw [le_iInf_iff]
    refine fun t ht_subset => iInf_le_of_le t ?_
    by_cases ht : forall i, P (t i)
    · exact iInf_le_of_le ht (iInf_le_of_le 

Depends on / 依赖: ENNReal, ENNReal.tsum_eq_top_of_eq_top, OuterMeasure, OuterMeasure.ofFunction_apply, hfi_top, ht_subset, hti_notMem, iInf_le_of_le, iInf_neg, le_antisymm, le_iInf, le_iInf_iff, le_rfl, m_top, not_false_eq_true, ofFunction_apply, simp_rw, top_le_iff, tsum_eq_top_of_eq_top
-/
theorem ofFunction_eq_iInf_mem {P : Set α -> Prop} (m_top : forall s, ¬ P s -> m s = ∞) (s : Set α) :
    OuterMeasure.ofFunction m m_empty s =
      ⨅ (t : Nat -> Set α) (_ : forall i, P (t i)) (_ : s subseteq ⋃ i, t i), ∑' i, m (t i) := by
  rw [OuterMeasure.ofFunction_apply]
  apply le_antisymm
  · exact le_iInf fun t => le_iInf fun _ => le_iInf fun h => iInf₂_le _ (by exact h)
  · simp_rw [le_iInf_iff]
    refine fun t ht_subset => iInf_le_of_le t ?_
    by_cases ht : forall i, P (t i)
    · exact iInf_le_of_le ht (iInf_le_of_le ht_subset le_rfl)
    · simp only [ht, not_false_eq_true, iInf_neg, top_le_iff]
      push Not at ht
      obtain ⟨i, hti_notMem⟩ := ht
      have hfi_top : m (t i) = ∞ := m_top _ hti_notMem
      exact ENNReal.tsum_eq_top_of_eq_top ⟨i, hfi_top⟩

variable {m m_empty}

/--
theorem `ofFunction_le` / 定理 `ofFunction_le`

English:
theorem ofFunction_le
  given: (s : Set α)
  statement: OuterMeasure.ofFunction m m_empty s <= m s
  proof: let f : Nat -> Set α := fun i => Nat.casesOn i s fun _ => ∅
iInf_le_of_le f
iInf_le_of_le (subset_iUnion f 0)
le_of_eq tsum_eq_single 0 by
        rintro (_ | i)
        · simp
        · simp [f, m_empty]

中文:
定理 ofFunction_le
  条件: (s : Set α)
  结论: OuterMeasure.ofFunction m m_empty s <= m s
  证明: let f : Nat -> Set α := fun i => Nat.casesOn i s fun _ => ∅
iInf_le_of_le f
iInf_le_of_le (subset_iUnion f 0)
le_of_eq tsum_eq_single 0 by
        rintro (_ | i)
        · simp
        · simp [f, m_empty]

Depends on / 依赖: Nat.casesOn, casesOn, iInf_le_of_le, le_of_eq, m_empty, subset_iUnion, tsum_eq_single
-/
theorem ofFunction_le (s : Set α) : OuterMeasure.ofFunction m m_empty s <= m s :=
  let f : Nat -> Set α := fun i => Nat.casesOn i s fun _ => ∅
iInf_le_of_le f
iInf_le_of_le (subset_iUnion f 0)
le_of_eq tsum_eq_single 0 by
        rintro (_ | i)
        · simp
        · simp [f, m_empty]

/--
theorem `ofFunction_eq` / 定理 `ofFunction_eq`

English:
theorem ofFunction_eq
  statement: (s : Set α) (m_mono : forall ⦃t : Set α⦄, s subseteq t -> m s <= m t)
  proof: le_antisymm (ofFunction_le s)
    le_iInf fun f => le_iInf fun hf => le_trans (m_mono hf) (m_subadd f)

中文:
定理 ofFunction_eq
  结论: (s : Set α) (m_mono : 对任意 ⦃t : Set α⦄, s subseteq t -> m s <= m t)
  证明: le_antisymm (ofFunction_le s)
    le_iInf fun f => le_iInf fun hf => le_trans (m_mono hf) (m_subadd f)

Depends on / 依赖: le_antisymm, le_iInf, le_trans, m_mono, m_subadd, ofFunction_le
-/
theorem ofFunction_eq (s : Set α) (m_mono : forall ⦃t : Set α⦄, s subseteq t -> m s <= m t)
    (m_subadd : forall s : Nat -> Set α, m (⋃ i, s i) <= ∑' i, m (s i)) :
    OuterMeasure.ofFunction m m_empty s = m s :=
le_antisymm (ofFunction_le s)
    le_iInf fun f => le_iInf fun hf => le_trans (m_mono hf) (m_subadd f)

/--
theorem `le_ofFunction` / 定理 `le_ofFunction`

English:
theorem le_ofFunction
  given: {μ : OuterMeasure α}
  proof: ⟨fun H s => le_trans (H s) (ofFunction_le s), fun H _ =>
    le_iInf fun f =>
      le_iInf fun hs =>
le_trans (μ.mono hs) le_trans (measure_iUnion_le f) ENNReal.tsum_le_tsum fun _ => H _⟩

中文:
定理 le_ofFunction
  条件: {μ : OuterMeasure α}
  证明: ⟨fun H s => le_trans (H s) (ofFunction_le s), fun H _ =>
    le_iInf fun f =>
      le_iInf fun hs =>
le_trans (μ.mono hs) le_trans (measure_iUnion_le f) ENNReal.tsum_le_tsum fun _ => H _⟩

Depends on / 依赖: ENNReal, ENNReal.tsum_le_tsum, le_iInf, le_trans, measure_iUnion_le, ofFunction_le, tsum_le_tsum
-/
theorem le_ofFunction {μ : OuterMeasure α} :
    μ <= OuterMeasure.ofFunction m m_empty ↔ forall s, μ s <= m s :=
  ⟨fun H s => le_trans (H s) (ofFunction_le s), fun H _ =>
    le_iInf fun f =>
      le_iInf fun hs =>
le_trans (μ.mono hs) le_trans (measure_iUnion_le f) ENNReal.tsum_le_tsum fun _ => H _⟩

/--
theorem `isGreatest_ofFunction` / 定理 `isGreatest_ofFunction`

English:
theorem isGreatest_ofFunction
  proof: ⟨fun _ => ofFunction_le _, fun _ => le_ofFunction.2⟩

中文:
定理 isGreatest_ofFunction
  证明: ⟨fun _ => ofFunction_le _, fun _ => le_ofFunction.2⟩

Depends on / 依赖: le_ofFunction, ofFunction_le
-/
theorem isGreatest_ofFunction :
    IsGreatest { μ : OuterMeasure α | forall s, μ s <= m s } (OuterMeasure.ofFunction m m_empty) :=
  ⟨fun _ => ofFunction_le _, fun _ => le_ofFunction.2⟩

/--
theorem `ofFunction_eq_sSup` / 定理 `ofFunction_eq_sSup`

English:
theorem ofFunction_eq_sSup
  statement: OuterMeasure.ofFunction m m_empty = sSup { μ | forall s, μ s <= m s }
  proof: (@isGreatest_ofFunction α m m_empty).isLUB.sSup_eq.symm

中文:
定理 ofFunction_eq_sSup
  结论: OuterMeasure.ofFunction m m_empty = sSup { μ | 对任意 s, μ s <= m s }
  证明: (@isGreatest_ofFunction α m m_empty).isLUB.sSup_eq.symm

Depends on / 依赖: isGreatest_ofFunction, isLUB.sSup_eq.symm, m_empty, sSup_eq
-/
theorem ofFunction_eq_sSup : OuterMeasure.ofFunction m m_empty = sSup { μ | forall s, μ s <= m s } :=
  (@isGreatest_ofFunction α m m_empty).isLUB.sSup_eq.symm

/--
theorem `ofFunction_union_of_top_of_nonempty_inter` / 定理 `ofFunction_union_of_top_of_nonempty_inter`

English:
theorem ofFunction_union_of_top_of_nonempty_inter
  statement: {s t : Set α}
  proof: by
  refine le_antisymm (measure_union_le _ _) (le_iInf₂ fun f hf => ?_)
  set μ := OuterMeasure.ofFunction m m_empty
  rcases Classical.em (exists i, (s inter f i).Nonempty ∧ (t inter f i).Nonempty) with (⟨i, hs, ht⟩ | he)
  · calc
      μ s + μ t <= ∞ := le_top
      _ = m (f i) := (h (f i) hs ht)

中文:
定理 ofFunction_union_of_top_of_nonempty_inter
  结论: {s t : Set α}
  证明: by
  refine le_antisymm (measure_union_le _ _) (le_iInf₂ fun f hf => ?_)
  set μ := OuterMeasure.ofFunction m m_empty
  rcases Classical.em (exists i, (s inter f i).Nonempty ∧ (t inter f i).Nonempty) with (⟨i, hs, ht⟩ | he)
  · calc
      μ s + μ t <= ∞ := le_top
      _ = m (f i) := (h (f i) hs ht)

Depends on / 依赖: Classical, Classical.em, Disjoint, ENNReal, ENNReal.le_tsum, Nonempty, OuterMeasure, OuterMeasure.ofFunction, disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, le_antisymm, le_top, le_tsum, m_empty, measure_union_le, ofFunction, subseteq
-/
theorem ofFunction_union_of_top_of_nonempty_inter {s t : Set α}
    (h : forall u, (s inter u).Nonempty -> (t inter u).Nonempty -> m u = ∞) :
    OuterMeasure.ofFunction m m_empty (s union t) =
      OuterMeasure.ofFunction m m_empty s + OuterMeasure.ofFunction m m_empty t := by
  refine le_antisymm (measure_union_le _ _) (le_iInf₂ fun f hf => ?_)
  set μ := OuterMeasure.ofFunction m m_empty
  rcases Classical.em (exists i, (s inter f i).Nonempty ∧ (t inter f i).Nonempty) with (⟨i, hs, ht⟩ | he)
  · calc
      μ s + μ t <= ∞ := le_top
      _ = m (f i) := (h (f i) hs ht).symm
      _ <= ∑' i, m (f i) := ENNReal.le_tsum i
  set I := fun s => { i : Nat | (s inter f i).Nonempty }
  have hd : Disjoint (I s) (I t) := disjoint_iff_inf_le.mpr fun i hi => he ⟨i, hi⟩
  have hI : forall u subseteq s union t, μ u <= ∑' i : I u, μ (f i) := fun u hu =>
    calc
      μ u <= μ (⋃ i : I u, f i) :=
        μ.mono fun x hx =>
          let ⟨i, hi⟩ := mem_iUnion.1 (hf (hu hx))
          mem_iUnion.2 ⟨⟨i, ⟨x, hx, hi⟩⟩, hi⟩
      _ <= ∑' i : I u, μ (f i) := measure_iUnion_le _
  calc
    μ s + μ t <= (∑' i : I s, μ (f i)) + ∑' i : I t, μ (f i) :=
      add_le_add (hI _ subset_union_left) (hI _ subset_union_right)
    _ = ∑' i : ↑(I s union I t), μ (f i) :=
      (ENNReal.summable.tsum_union_disjoint (f := fun i => μ (f i)) hd ENNReal.summable).symm
    _ <= ∑' i, μ (f i) :=
      (ENNReal.summable.tsum_le_tsum_of_inj (↑) Subtype.coe_injective (fun _ _ => zero_le)
        (fun _ => le_rfl) ENNReal.summable)
    _ <= ∑' i, m (f i) := ENNReal.tsum_le_tsum fun i => ofFunction_le _

/--
theorem `comap_ofFunction` / 定理 `comap_ofFunction`

English:
theorem comap_ofFunction
  given: {β} (f : β -> α) (h : Monotone m ∨ Surjective f)
  proof: by
  refine le_antisymm (le_ofFunction.2 fun s => ?_) fun s => ?_
  · rw [comap_apply]
    apply ofFunction_le
  · rw [comap_apply, ofFunction_apply, ofFunction_apply]
    refine iInf_mono' fun t => ⟨fun k => f ⁻¹' t k, ?_⟩
    refine iInf_mono' fun ht => ?_
    rw [Set.image_subset_iff]; rw [preima

中文:
定理 comap_ofFunction
  条件: {β} (f : β -> α) (h : Monotone m ∨ Surjective f)
  证明: by
  refine le_antisymm (le_ofFunction.2 fun s => ?_) fun s => ?_
  · rw [comap_apply]
    apply ofFunction_le
  · rw [comap_apply, ofFunction_apply, ofFunction_apply]
    refine iInf_mono' fun t => ⟨fun k => f ⁻¹' t k, ?_⟩
    refine iInf_mono' fun ht => ?_
    rw [Set.image_subset_iff]; rw [preima

Depends on / 依赖: ENNReal, ENNReal.tsum_le_tsum, Set.image_subset_iff, comap_apply, congr_arg, exacts, hr.image_preimage, iInf_mono, image_preimage, image_preimage_subset, image_subset_iff, le_antisymm, le_ofFunction, ofFunction_apply, ofFunction_le, preimage_iUnion, tsum_le_tsum
-/
theorem comap_ofFunction {β} (f : β -> α) (h : Monotone m ∨ Surjective f) :
    comap f (OuterMeasure.ofFunction m m_empty) =
      OuterMeasure.ofFunction (fun s => m (f '' s)) (by simp; simp [m_empty]) := by
  refine le_antisymm (le_ofFunction.2 fun s => ?_) fun s => ?_
  · rw [comap_apply]
    apply ofFunction_le
  · rw [comap_apply, ofFunction_apply, ofFunction_apply]
    refine iInf_mono' fun t => ⟨fun k => f ⁻¹' t k, ?_⟩
    refine iInf_mono' fun ht => ?_
    rw [Set.image_subset_iff]; rw [preimage_iUnion] at ht
    refine ⟨ht, ENNReal.tsum_le_tsum fun n => ?_⟩
    rcases h with hl | hr
    exacts [hl (image_preimage_subset _ _), (congr_arg m (hr.image_preimage (t n))).le]

/--
theorem `map_ofFunction_le` / 定理 `map_ofFunction_le`

English:
theorem map_ofFunction_le
  given: {β} (f : α -> β)
  proof: le_ofFunction.2 fun s => by
    rw [map_apply]
    apply ofFunction_le

中文:
定理 map_ofFunction_le
  条件: {β} (f : α -> β)
  证明: le_ofFunction.2 fun s => by
    rw [map_apply]
    apply ofFunction_le

Depends on / 依赖: le_ofFunction, map_apply, ofFunction_le
-/
theorem map_ofFunction_le {β} (f : α -> β) :
    map f (OuterMeasure.ofFunction m m_empty) <=
      OuterMeasure.ofFunction (fun s => m (f ⁻¹' s)) m_empty :=
  le_ofFunction.2 fun s => by
    rw [map_apply]
    apply ofFunction_le

/--
theorem `map_ofFunction` / 定理 `map_ofFunction`

English:
theorem map_ofFunction
  given: {β} {f : α -> β} (hf : Injective f)
  proof: by
  refine (map_ofFunction_le _).antisymm fun s => ?_
  simp only [ofFunction_apply, map_apply, le_iInf_iff]
  intro t ht
  refine iInf_le_of_le (fun n => (range f)ᶜ union f '' t n) (iInf_le_of_le ?_ ?_)
  · rw [← union_iUnion, ← inter_subset, ← image_preimage_eq_inter_range, ← image_iUnion]
    ex

中文:
定理 map_ofFunction
  条件: {β} {f : α -> β} (hf : Injective f)
  证明: by
  refine (map_ofFunction_le _).antisymm fun s => ?_
  simp only [ofFunction_apply, map_apply, le_iInf_iff]
  intro t ht
  refine iInf_le_of_le (fun n => (range f)ᶜ union f '' t n) (iInf_le_of_le ?_ ?_)
  · rw [← union_iUnion, ← inter_subset, ← image_preimage_eq_inter_range, ← image_iUnion]
    ex

Depends on / 依赖: ENNReal, ENNReal.tsum_le_tsum, antisymm, hf.preimage_image, iInf_le_of_le, image_iUnion, image_mono, image_preimage_eq_inter_range, inter_subset, le_iInf_iff, le_of_eq, map_apply, map_ofFunction_le, ofFunction_apply, preimage_image, tsum_le_tsum, union_iUnion
-/
theorem map_ofFunction {β} {f : α -> β} (hf : Injective f) :
    map f (OuterMeasure.ofFunction m m_empty) =
      OuterMeasure.ofFunction (fun s => m (f ⁻¹' s)) m_empty := by
  refine (map_ofFunction_le _).antisymm fun s => ?_
  simp only [ofFunction_apply, map_apply, le_iInf_iff]
  intro t ht
  refine iInf_le_of_le (fun n => (range f)ᶜ union f '' t n) (iInf_le_of_le ?_ ?_)
  · rw [← union_iUnion, ← inter_subset, ← image_preimage_eq_inter_range, ← image_iUnion]
    exact image_mono ht
  · refine ENNReal.tsum_le_tsum fun n => le_of_eq ?_
    simp [hf.preimage_image]

-- TODO (kmill): change `m (t ∩ s)` to `m (s ∩ t)`
/--
theorem `restrict_ofFunction` / 定理 `restrict_ofFunction`

English:
theorem restrict_ofFunction
  given: (s : Set α) (hm : Monotone m)
  proof: by
      rw [restrict]
      simp only [inter_comm _ s, LinearMap.comp_apply]
      rw [comap_ofFunction _ (Or.inl hm)]
      simp only [map_ofFunction Subtype.coe_injective, Subtype.image_preimage_coe]

中文:
定理 restrict_ofFunction
  条件: (s : Set α) (hm : Monotone m)
  证明: by
      rw [restrict]
      simp only [inter_comm _ s, LinearMap.comp_apply]
      rw [comap_ofFunction _ (Or.inl hm)]
      simp only [map_ofFunction Subtype.coe_injective, Subtype.image_preimage_coe]

Depends on / 依赖: LinearMap, LinearMap.comp_apply, Or.inl, Subtype, Subtype.coe_injective, Subtype.image_preimage_coe, coe_injective, comap_ofFunction, comp_apply, image_preimage_coe, inter_comm, map_ofFunction, restrict
-/
theorem restrict_ofFunction (s : Set α) (hm : Monotone m) :
    restrict s (OuterMeasure.ofFunction m m_empty) =
      OuterMeasure.ofFunction (fun t => m (t inter s)) (by simp; simp [m_empty]) := by
      rw [restrict]
      simp only [inter_comm _ s, LinearMap.comp_apply]
      rw [comap_ofFunction _ (Or.inl hm)]
      simp only [map_ofFunction Subtype.coe_injective, Subtype.image_preimage_coe]

/--
theorem `smul_ofFunction` / 定理 `smul_ofFunction`

English:
theorem smul_ofFunction
  given: {c : Real>=0∞} (hc : c != ∞)
  statement: c • OuterMeasure.ofFunction m m_empty =
  proof: by
  ext1 s
  have : Nonempty { t : Nat -> Set α // s subseteq ⋃ i, t i } := ⟨⟨fun _ => s, subset_iUnion (fun _ => s) 0⟩⟩
  simp only [smul_apply, ofFunction_apply, ENNReal.tsum_mul_left, Pi.smul_apply, smul_eq_mul,
  iInf_subtype']
  rw [ENNReal.mul_iInf fun h => (hc h).elim]

中文:
定理 smul_ofFunction
  条件: {c : 实数>=0∞} (hc : c != ∞)
  结论: c • OuterMeasure.ofFunction m m_empty =
  证明: by
  ext1 s
  have : Nonempty { t : Nat -> Set α // s subseteq ⋃ i, t i } := ⟨⟨fun _ => s, subset_iUnion (fun _ => s) 0⟩⟩
  simp only [smul_apply, ofFunction_apply, ENNReal.tsum_mul_left, Pi.smul_apply, smul_eq_mul,
  iInf_subtype']
  rw [ENNReal.mul_iInf fun h => (hc h).elim]

Depends on / 依赖: ENNReal, ENNReal.mul_iInf, ENNReal.tsum_mul_left, Nonempty, Pi.smul_apply, iInf_subtype, mul_iInf, ofFunction_apply, smul_apply, smul_eq_mul, subset_iUnion, subseteq, tsum_mul_left
-/
theorem smul_ofFunction {c : Real>=0∞} (hc : c != ∞) : c • OuterMeasure.ofFunction m m_empty =
    OuterMeasure.ofFunction (c • m) (by simp [m_empty]) := by
  ext1 s
  have : Nonempty { t : Nat -> Set α // s subseteq ⋃ i, t i } := ⟨⟨fun _ => s, subset_iUnion (fun _ => s) 0⟩⟩
  simp only [smul_apply, ofFunction_apply, ENNReal.tsum_mul_left, Pi.smul_apply, smul_eq_mul,
  iInf_subtype']
  rw [ENNReal.mul_iInf fun h => (hc h).elim]

end OfFunction

section BoundedBy

variable {α : Type*} (m : Set α -> Real>=0∞)

/--
Definition of `boundedBy` / `boundedBy` 的定义

English:
definition boundedBy
  signature: : OuterMeasure α
  body: OuterMeasure.ofFunction (fun s => ⨆ _ : s.Nonempty, m s) (by simp [Set.not_nonempty_empty])

中文:
定义 boundedBy
  签名: : OuterMeasure α
  定义体: OuterMeasure.ofFunction (fun s => ⨆ _ : s.Nonempty, m s) (by simp [Set.not_nonempty_empty])

Depends on / 依赖: Nonempty, OuterMeasure, OuterMeasure.ofFunction, Set.not_nonempty_empty, not_nonempty_empty, ofFunction, s.Nonempty
-/
def boundedBy : OuterMeasure α :=
  OuterMeasure.ofFunction (fun s => ⨆ _ : s.Nonempty, m s) (by simp [Set.not_nonempty_empty])

variable {m}

/--
theorem `boundedBy_le` / 定理 `boundedBy_le`

English:
theorem boundedBy_le
  given: (s : Set α)
  statement: boundedBy m s <= m s
  proof: (ofFunction_le _).trans iSup_const_le

中文:
定理 boundedBy_le
  条件: (s : Set α)
  结论: boundedBy m s <= m s
  证明: (ofFunction_le _).trans iSup_const_le

Depends on / 依赖: iSup_const_le, ofFunction_le
-/
theorem boundedBy_le (s : Set α) : boundedBy m s <= m s :=
  (ofFunction_le _).trans iSup_const_le

/--
theorem `boundedBy_eq_ofFunction` / 定理 `boundedBy_eq_ofFunction`

English:
theorem boundedBy_eq_ofFunction
  given: (m_empty : m ∅ = 0) (s : Set α)
  proof: by
  have : (fun s : Set α => ⨆ _ : s.Nonempty, m s) = m := by
    ext1 t
    rcases t.eq_empty_or_nonempty with h | h <;> simp [h, Set.not_nonempty_empty, m_empty]
  simp [boundedBy, this]

中文:
定理 boundedBy_eq_ofFunction
  条件: (m_empty : m ∅ = 0) (s : Set α)
  证明: by
  have : (fun s : Set α => ⨆ _ : s.Nonempty, m s) = m := by
    ext1 t
    rcases t.eq_empty_or_nonempty with h | h <;> simp [h, Set.not_nonempty_empty, m_empty]
  simp [boundedBy, this]

Depends on / 依赖: Nonempty, Set.not_nonempty_empty, boundedBy, eq_empty_or_nonempty, m_empty, not_nonempty_empty, s.Nonempty, t.eq_empty_or_nonempty
-/
theorem boundedBy_eq_ofFunction (m_empty : m ∅ = 0) (s : Set α) :
    boundedBy m s = OuterMeasure.ofFunction m m_empty s := by
  have : (fun s : Set α => ⨆ _ : s.Nonempty, m s) = m := by
    ext1 t
    rcases t.eq_empty_or_nonempty with h | h <;> simp [h, Set.not_nonempty_empty, m_empty]
  simp [boundedBy, this]

/--
theorem `boundedBy_apply` / 定理 `boundedBy_apply`

English:
theorem boundedBy_apply
  given: (s : Set α)
  proof: by
  simp [boundedBy, ofFunction_apply]

中文:
定理 boundedBy_apply
  条件: (s : Set α)
  证明: by
  simp [boundedBy, ofFunction_apply]

Depends on / 依赖: boundedBy, ofFunction_apply
-/
theorem boundedBy_apply (s : Set α) :
    boundedBy m s = ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t),
                      ∑' n, ⨆ _ : (t n).Nonempty, m (t n) := by
  simp [boundedBy, ofFunction_apply]

/--
theorem `boundedBy_eq` / 定理 `boundedBy_eq`

English:
theorem boundedBy_eq
  statement: (s : Set α) (m_empty : m ∅ = 0) (m_mono : forall ⦃t : Set α⦄, s subseteq t -> m s <= m t)
  proof: by
  rw [boundedBy_eq_ofFunction m_empty]; rw [ofFunction_eq s m_mono m_subadd]

@[simp]

中文:
定理 boundedBy_eq
  结论: (s : Set α) (m_empty : m ∅ = 0) (m_mono : 对任意 ⦃t : Set α⦄, s subseteq t -> m s <= m t)
  证明: by
  rw [boundedBy_eq_ofFunction m_empty]; rw [ofFunction_eq s m_mono m_subadd]

@[simp]

Depends on / 依赖: boundedBy_eq_ofFunction, m_empty, m_mono, m_subadd, ofFunction_eq
-/
theorem boundedBy_eq (s : Set α) (m_empty : m ∅ = 0) (m_mono : forall ⦃t : Set α⦄, s subseteq t -> m s <= m t)
    (m_subadd : forall s : Nat -> Set α, m (⋃ i, s i) <= ∑' i, m (s i)) : boundedBy m s = m s := by
  rw [boundedBy_eq_ofFunction m_empty]; rw [ofFunction_eq s m_mono m_subadd]

@[simp]
/--
theorem `boundedBy_eq_self` / 定理 `boundedBy_eq_self`

English:
theorem boundedBy_eq_self
  given: (m : OuterMeasure α)
  statement: boundedBy m = m
  proof: ext fun _ => boundedBy_eq _ measure_empty (fun _ ht => measure_mono ht) measure_iUnion_le

中文:
定理 boundedBy_eq_self
  条件: (m : OuterMeasure α)
  结论: boundedBy m = m
  证明: ext fun _ => boundedBy_eq _ measure_empty (fun _ ht => measure_mono ht) measure_iUnion_le

Depends on / 依赖: boundedBy_eq, measure_empty, measure_iUnion_le, measure_mono
-/
theorem boundedBy_eq_self (m : OuterMeasure α) : boundedBy m = m :=
  ext fun _ => boundedBy_eq _ measure_empty (fun _ ht => measure_mono ht) measure_iUnion_le

/--
theorem `le_boundedBy` / 定理 `le_boundedBy`

English:
theorem le_boundedBy
  given: {μ : OuterMeasure α}
  statement: μ <= boundedBy m ↔ forall s, μ s <= m s
  proof: by
  rw [boundedBy]; rw [le_ofFunction]; rw [forall_congr']; intro s
  rcases s.eq_empty_or_nonempty with h | h <;> simp [h, Set.not_nonempty_empty]

中文:
定理 le_boundedBy
  条件: {μ : OuterMeasure α}
  结论: μ <= boundedBy m ↔ 对任意 s, μ s <= m s
  证明: by
  rw [boundedBy]; rw [le_ofFunction]; rw [forall_congr']; intro s
  rcases s.eq_empty_or_nonempty with h | h <;> simp [h, Set.not_nonempty_empty]

Depends on / 依赖: Set.not_nonempty_empty, boundedBy, eq_empty_or_nonempty, forall_congr, le_ofFunction, not_nonempty_empty, s.eq_empty_or_nonempty
-/
theorem le_boundedBy {μ : OuterMeasure α} : μ <= boundedBy m ↔ forall s, μ s <= m s := by
  rw [boundedBy]; rw [le_ofFunction]; rw [forall_congr']; intro s
  rcases s.eq_empty_or_nonempty with h | h <;> simp [h, Set.not_nonempty_empty]

/--
theorem `le_boundedBy'` / 定理 `le_boundedBy'`

English:
theorem le_boundedBy'
  given: {μ : OuterMeasure α}
  proof: by
  rw [le_boundedBy]; rw [forall_congr']
  intro s
  rcases s.eq_empty_or_nonempty with h | h <;> simp [h]

@[simp]

中文:
定理 le_boundedBy'
  条件: {μ : OuterMeasure α}
  证明: by
  rw [le_boundedBy]; rw [forall_congr']
  intro s
  rcases s.eq_empty_or_nonempty with h | h <;> simp [h]

@[simp]

Depends on / 依赖: eq_empty_or_nonempty, forall_congr, le_boundedBy, s.eq_empty_or_nonempty
-/
theorem le_boundedBy' {μ : OuterMeasure α} :
    μ <= boundedBy m ↔ forall s : Set α, s.Nonempty -> μ s <= m s := by
  rw [le_boundedBy]; rw [forall_congr']
  intro s
  rcases s.eq_empty_or_nonempty with h | h <;> simp [h]

@[simp]
/--
theorem `boundedBy_top` / 定理 `boundedBy_top`

English:
theorem boundedBy_top
  statement: boundedBy (⊤ : Set α -> Real>=0∞) = ⊤
  proof: by
  rw [eq_top_iff]; rw [le_boundedBy']
  intro s hs
  rw [top_apply hs]
  exact le_rfl

@[simp]

中文:
定理 boundedBy_top
  结论: boundedBy (⊤ : Set α -> 实数>=0∞) = ⊤
  证明: by
  rw [eq_top_iff]; rw [le_boundedBy']
  intro s hs
  rw [top_apply hs]
  exact le_rfl

@[simp]

Depends on / 依赖: eq_top_iff, le_boundedBy, le_rfl, top_apply
-/
theorem boundedBy_top : boundedBy (⊤ : Set α -> Real>=0∞) = ⊤ := by
  rw [eq_top_iff]; rw [le_boundedBy']
  intro s hs
  rw [top_apply hs]
  exact le_rfl

@[simp]
/--
theorem `boundedBy_zero` / 定理 `boundedBy_zero`

English:
theorem boundedBy_zero
  statement: boundedBy (0 : Set α -> Real>=0∞) = 0
  proof: by
  rw [← coe_bot]; rw [eq_bot_iff]
  apply boundedBy_le

中文:
定理 boundedBy_zero
  结论: boundedBy (0 : Set α -> 实数>=0∞) = 0
  证明: by
  rw [← coe_bot]; rw [eq_bot_iff]
  apply boundedBy_le

Depends on / 依赖: boundedBy_le, coe_bot, eq_bot_iff
-/
theorem boundedBy_zero : boundedBy (0 : Set α -> Real>=0∞) = 0 := by
  rw [← coe_bot]; rw [eq_bot_iff]
  apply boundedBy_le

/--
theorem `smul_boundedBy` / 定理 `smul_boundedBy`

English:
theorem smul_boundedBy
  given: {c : Real>=0∞} (hc : c != ∞)
  statement: c • boundedBy m = boundedBy (c • m)
  proof: by
  simp only [boundedBy, smul_ofFunction hc]
  congr 1 with s : 1
  rcases s.eq_empty_or_nonempty with (rfl | hs) <;> simp [*]

中文:
定理 smul_boundedBy
  条件: {c : 实数>=0∞} (hc : c != ∞)
  结论: c • boundedBy m = boundedBy (c • m)
  证明: by
  simp only [boundedBy, smul_ofFunction hc]
  congr 1 with s : 1
  rcases s.eq_empty_or_nonempty with (rfl | hs) <;> simp [*]

Depends on / 依赖: boundedBy, eq_empty_or_nonempty, s.eq_empty_or_nonempty, smul_ofFunction
-/
theorem smul_boundedBy {c : Real>=0∞} (hc : c != ∞) : c • boundedBy m = boundedBy (c • m) := by
  simp only [boundedBy, smul_ofFunction hc]
  congr 1 with s : 1
  rcases s.eq_empty_or_nonempty with (rfl | hs) <;> simp [*]

/--
theorem `comap_boundedBy` / 定理 `comap_boundedBy`

English:
theorem comap_boundedBy
  statement: {β} (f : β -> α)
  proof: by
  refine (comap_ofFunction _ ?_).trans ?_
  · refine h.imp (fun H s t hst => iSup_le fun hs => ?_) id
    have ht : t.Nonempty := hs.mono hst
    exact (@H ⟨s, hs⟩ ⟨t, ht⟩ hst).trans (le_iSup (fun _ : t.Nonempty => m t) ht)
  · dsimp only [boundedBy]
    congr with s : 1
    rw [image_nonempty]

中文:
定理 comap_boundedBy
  结论: {β} (f : β -> α)
  证明: by
  refine (comap_ofFunction _ ?_).trans ?_
  · refine h.imp (fun H s t hst => iSup_le fun hs => ?_) id
    have ht : t.Nonempty := hs.mono hst
    exact (@H ⟨s, hs⟩ ⟨t, ht⟩ hst).trans (le_iSup (fun _ : t.Nonempty => m t) ht)
  · dsimp only [boundedBy]
    congr with s : 1
    rw [image_nonempty]

Depends on / 依赖: Nonempty, boundedBy, comap_ofFunction, h.imp, hs.mono, iSup_le, image_nonempty, le_iSup, t.Nonempty
-/
theorem comap_boundedBy {β} (f : β -> α)
    (h : (Monotone fun s : { s : Set α // s.Nonempty } => m s) ∨ Surjective f) :
    comap f (boundedBy m) = boundedBy fun s => m (f '' s) := by
  refine (comap_ofFunction _ ?_).trans ?_
  · refine h.imp (fun H s t hst => iSup_le fun hs => ?_) id
    have ht : t.Nonempty := hs.mono hst
    exact (@H ⟨s, hs⟩ ⟨t, ht⟩ hst).trans (le_iSup (fun _ : t.Nonempty => m t) ht)
  · dsimp only [boundedBy]
    congr with s : 1
    rw [image_nonempty]

/--
theorem `boundedBy_union_of_top_of_nonempty_inter` / 定理 `boundedBy_union_of_top_of_nonempty_inter`

English:
theorem boundedBy_union_of_top_of_nonempty_inter
  statement: {s t : Set α}
  proof: ofFunction_union_of_top_of_nonempty_inter fun u hs ht =>
top_unique (h u hs ht).ge.trans le_iSup (fun _ => m u) (hs.mono inter_subset_right)

中文:
定理 boundedBy_union_of_top_of_nonempty_inter
  结论: {s t : Set α}
  证明: ofFunction_union_of_top_of_nonempty_inter fun u hs ht =>
top_unique (h u hs ht).ge.trans le_iSup (fun _ => m u) (hs.mono inter_subset_right)

Depends on / 依赖: ge.trans, hs.mono, inter_subset_right, le_iSup, ofFunction_union_of_top_of_nonempty_inter, top_unique
-/
theorem boundedBy_union_of_top_of_nonempty_inter {s t : Set α}
    (h : forall u, (s inter u).Nonempty -> (t inter u).Nonempty -> m u = ∞) :
    boundedBy m (s union t) = boundedBy m s + boundedBy m t :=
  ofFunction_union_of_top_of_nonempty_inter fun u hs ht =>
top_unique (h u hs ht).ge.trans le_iSup (fun _ => m u) (hs.mono inter_subset_right)

end BoundedBy

section sInfGen

variable {α : Type*}

/--
Definition of `sInfGen` / `sInfGen` 的定义

English:
definition sInfGen
  signature: (m : Set (OuterMeasure α)) (s : Set α)
  body: ⨅ (μ : OuterMeasure α) (_ : μ in m), μ s

中文:
定义 sInfGen
  签名: (m : Set (OuterMeasure α)) (s : Set α)
  定义体: ⨅ (μ : OuterMeasure α) (_ : μ in m), μ s

Depends on / 依赖: OuterMeasure
-/
def sInfGen (m : Set (OuterMeasure α)) (s : Set α) : Real>=0∞ :=
  ⨅ (μ : OuterMeasure α) (_ : μ in m), μ s

/--
theorem `sInfGen_def` / 定理 `sInfGen_def`

English:
theorem sInfGen_def
  given: (m : Set (OuterMeasure α)) (t : Set α)
  proof: rfl

中文:
定理 sInfGen_def
  条件: (m : Set (OuterMeasure α)) (t : Set α)
  证明: rfl
-/
theorem sInfGen_def (m : Set (OuterMeasure α)) (t : Set α) :
    sInfGen m t = ⨅ (μ : OuterMeasure α) (_ : μ in m), μ t :=
  rfl

/--
theorem `sInf_eq_boundedBy_sInfGen` / 定理 `sInf_eq_boundedBy_sInfGen`

English:
theorem sInf_eq_boundedBy_sInfGen
  given: (m : Set (OuterMeasure α))
  proof: by
  refine le_antisymm ?_ ?_
  · refine le_boundedBy.2 fun s => le_iInf₂ fun μ hμ => ?_
    apply sInf_le hμ
  · refine le_sInf ?_
    intro μ hμ t
    exact le_trans (boundedBy_le t) (iInf₂_le μ hμ)

中文:
定理 sInf_eq_boundedBy_sInfGen
  条件: (m : Set (OuterMeasure α))
  证明: by
  refine le_antisymm ?_ ?_
  · refine le_boundedBy.2 fun s => le_iInf₂ fun μ hμ => ?_
    apply sInf_le hμ
  · refine le_sInf ?_
    intro μ hμ t
    exact le_trans (boundedBy_le t) (iInf₂_le μ hμ)

Depends on / 依赖: boundedBy_le, le_antisymm, le_boundedBy, le_sInf, le_trans, sInf_le
-/
theorem sInf_eq_boundedBy_sInfGen (m : Set (OuterMeasure α)) :
    sInf m = OuterMeasure.boundedBy (sInfGen m) := by
  refine le_antisymm ?_ ?_
  · refine le_boundedBy.2 fun s => le_iInf₂ fun μ hμ => ?_
    apply sInf_le hμ
  · refine le_sInf ?_
    intro μ hμ t
    exact le_trans (boundedBy_le t) (iInf₂_le μ hμ)

/--
theorem `iSup_sInfGen_nonempty` / 定理 `iSup_sInfGen_nonempty`

English:
theorem iSup_sInfGen_nonempty
  given: {m : Set (OuterMeasure α)} (h : m.Nonempty) (t : Set α)
  proof: by
  rcases t.eq_empty_or_nonempty with (rfl | ht)
  · simp [biInf_const h]
  · simp [ht, sInfGen_def]

中文:
定理 iSup_sInfGen_nonempty
  条件: {m : Set (OuterMeasure α)} (h : m.Nonempty) (t : Set α)
  证明: by
  rcases t.eq_empty_or_nonempty with (rfl | ht)
  · simp [biInf_const h]
  · simp [ht, sInfGen_def]

Depends on / 依赖: biInf_const, eq_empty_or_nonempty, sInfGen_def, t.eq_empty_or_nonempty
-/
theorem iSup_sInfGen_nonempty {m : Set (OuterMeasure α)} (h : m.Nonempty) (t : Set α) :
    ⨆ _ : t.Nonempty, sInfGen m t = ⨅ (μ : OuterMeasure α) (_ : μ in m), μ t := by
  rcases t.eq_empty_or_nonempty with (rfl | ht)
  · simp [biInf_const h]
  · simp [ht, sInfGen_def]

/--
theorem `sInf_apply` / 定理 `sInf_apply`

English:
theorem sInf_apply
  given: {m : Set (OuterMeasure α)} {s : Set α} (h : m.Nonempty)
  proof: by
  simp_rw [sInf_eq_boundedBy_sInfGen, boundedBy_apply, iSup_sInfGen_nonempty h]

中文:
定理 sInf_apply
  条件: {m : Set (OuterMeasure α)} {s : Set α} (h : m.Nonempty)
  证明: by
  simp_rw [sInf_eq_boundedBy_sInfGen, boundedBy_apply, iSup_sInfGen_nonempty h]

Depends on / 依赖: boundedBy_apply, iSup_sInfGen_nonempty, sInf_eq_boundedBy_sInfGen, simp_rw
-/
theorem sInf_apply {m : Set (OuterMeasure α)} {s : Set α} (h : m.Nonempty) :
    sInf m s =
      ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t), ∑' n, ⨅ (μ : OuterMeasure α) (_ : μ in m), μ (t n) := by
  simp_rw [sInf_eq_boundedBy_sInfGen, boundedBy_apply, iSup_sInfGen_nonempty h]

/--
theorem `sInf_apply'` / 定理 `sInf_apply'`

English:
theorem sInf_apply'
  given: {m : Set (OuterMeasure α)} {s : Set α} (h : s.Nonempty)
  proof: m.eq_empty_or_nonempty.elim (fun hm => by simp [hm, h]) sInf_apply

中文:
定理 sInf_apply'
  条件: {m : Set (OuterMeasure α)} {s : Set α} (h : s.Nonempty)
  证明: m.eq_empty_or_nonempty.elim (fun hm => by simp [hm, h]) sInf_apply

Depends on / 依赖: eq_empty_or_nonempty, m.eq_empty_or_nonempty.elim, sInf_apply
-/
theorem sInf_apply' {m : Set (OuterMeasure α)} {s : Set α} (h : s.Nonempty) :
    sInf m s =
      ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t), ∑' n, ⨅ (μ : OuterMeasure α) (_ : μ in m), μ (t n) :=
  m.eq_empty_or_nonempty.elim (fun hm => by simp [hm, h]) sInf_apply

/--
theorem `iInf_apply` / 定理 `iInf_apply`

English:
theorem iInf_apply
  given: {ι} [Nonempty ι] (m : ι -> OuterMeasure α) (s : Set α)
  proof: by
  rw [iInf]; rw [sInf_apply (range_nonempty m)]
  simp only [iInf_range]

中文:
定理 iInf_apply
  条件: {ι} [Nonempty ι] (m : ι -> OuterMeasure α) (s : Set α)
  证明: by
  rw [iInf]; rw [sInf_apply (range_nonempty m)]
  simp only [iInf_range]

Depends on / 依赖: iInf_range, range_nonempty, sInf_apply
-/
theorem iInf_apply {ι} [Nonempty ι] (m : ι -> OuterMeasure α) (s : Set α) :
    (⨅ i, m i) s = ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t), ∑' n, ⨅ i, m i (t n) := by
  rw [iInf]; rw [sInf_apply (range_nonempty m)]
  simp only [iInf_range]

/--
theorem `iInf_apply'` / 定理 `iInf_apply'`

English:
theorem iInf_apply'
  given: {ι} (m : ι -> OuterMeasure α) {s : Set α} (hs : s.Nonempty)
  proof: by
  rw [iInf]; rw [sInf_apply' hs]
  simp only [iInf_range]

中文:
定理 iInf_apply'
  条件: {ι} (m : ι -> OuterMeasure α) {s : Set α} (hs : s.Nonempty)
  证明: by
  rw [iInf]; rw [sInf_apply' hs]
  simp only [iInf_range]

Depends on / 依赖: iInf_range, sInf_apply
-/
theorem iInf_apply' {ι} (m : ι -> OuterMeasure α) {s : Set α} (hs : s.Nonempty) :
    (⨅ i, m i) s = ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t), ∑' n, ⨅ i, m i (t n) := by
  rw [iInf]; rw [sInf_apply' hs]
  simp only [iInf_range]

/--
theorem `biInf_apply` / 定理 `biInf_apply`

English:
theorem biInf_apply
  given: {ι} {I : Set ι} (hI : I.Nonempty) (m : ι -> OuterMeasure α) (s : Set α)
  proof: by
  have := hI.to_subtype
  simp only [← iInf_subtype'', iInf_apply]

中文:
定理 biInf_apply
  条件: {ι} {I : Set ι} (hI : I.Nonempty) (m : ι -> OuterMeasure α) (s : Set α)
  证明: by
  have := hI.to_subtype
  simp only [← iInf_subtype'', iInf_apply]

Depends on / 依赖: hI.to_subtype, iInf_apply, iInf_subtype, to_subtype
-/
theorem biInf_apply {ι} {I : Set ι} (hI : I.Nonempty) (m : ι -> OuterMeasure α) (s : Set α) :
    (⨅ i in I, m i) s = ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t), ∑' n, ⨅ i in I, m i (t n) := by
  have := hI.to_subtype
  simp only [← iInf_subtype'', iInf_apply]

/--
theorem `biInf_apply'` / 定理 `biInf_apply'`

English:
theorem biInf_apply'
  given: {ι} (I : Set ι) (m : ι -> OuterMeasure α) {s : Set α} (hs : s.Nonempty)
  proof: by
  simp only [← iInf_subtype'', iInf_apply' _ hs]

中文:
定理 biInf_apply'
  条件: {ι} (I : Set ι) (m : ι -> OuterMeasure α) {s : Set α} (hs : s.Nonempty)
  证明: by
  simp only [← iInf_subtype'', iInf_apply' _ hs]

Depends on / 依赖: iInf_apply, iInf_subtype
-/
theorem biInf_apply' {ι} (I : Set ι) (m : ι -> OuterMeasure α) {s : Set α} (hs : s.Nonempty) :
    (⨅ i in I, m i) s = ⨅ (t : Nat -> Set α) (_ : s subseteq iUnion t), ∑' n, ⨅ i in I, m i (t n) := by
  simp only [← iInf_subtype'', iInf_apply' _ hs]

/--
theorem `map_iInf_le` / 定理 `map_iInf_le`

English:
theorem map_iInf_le
  given: {ι β} (f : α -> β) (m : ι -> OuterMeasure α)
  proof: (map_mono f).map_iInf_le

中文:
定理 map_iInf_le
  条件: {ι β} (f : α -> β) (m : ι -> OuterMeasure α)
  证明: (map_mono f).map_iInf_le

Depends on / 依赖: map_iInf_le, map_mono
-/
theorem map_iInf_le {ι β} (f : α -> β) (m : ι -> OuterMeasure α) :
    map f (⨅ i, m i) <= ⨅ i, map f (m i) :=
  (map_mono f).map_iInf_le

/--
theorem `comap_iInf` / 定理 `comap_iInf`

English:
theorem comap_iInf
  given: {ι β} (f : α -> β) (m : ι -> OuterMeasure β)
  proof: by
  refine ext_nonempty fun s hs => ?_
  refine ((comap_mono f).map_iInf_le s).antisymm ?_
  simp only [comap_apply, iInf_apply' _ hs, iInf_apply' _ (hs.image _), le_iInf_iff,
    Set.image_subset_iff, preimage_iUnion]
  refine fun t ht => iInf_le_of_le _ (iInf_le_of_le ht <| ENNReal.tsum_le_tsum f

中文:
定理 comap_iInf
  条件: {ι β} (f : α -> β) (m : ι -> OuterMeasure β)
  证明: by
  refine ext_nonempty fun s hs => ?_
  refine ((comap_mono f).map_iInf_le s).antisymm ?_
  simp only [comap_apply, iInf_apply' _ hs, iInf_apply' _ (hs.image _), le_iInf_iff,
    Set.image_subset_iff, preimage_iUnion]
  refine fun t ht => iInf_le_of_le _ (iInf_le_of_le ht <| ENNReal.tsum_le_tsum f

Depends on / 依赖: ENNReal, ENNReal.tsum_le_tsum, Set.image_subset_iff, antisymm, comap_apply, comap_mono, ext_nonempty, hs.image, iInf_apply, iInf_le_of_le, iInf_mono, image_preimage_subset, image_subset_iff, le_iInf_iff, map_iInf_le, preimage_iUnion, tsum_le_tsum
-/
theorem comap_iInf {ι β} (f : α -> β) (m : ι -> OuterMeasure β) :
    comap f (⨅ i, m i) = ⨅ i, comap f (m i) := by
  refine ext_nonempty fun s hs => ?_
  refine ((comap_mono f).map_iInf_le s).antisymm ?_
  simp only [comap_apply, iInf_apply' _ hs, iInf_apply' _ (hs.image _), le_iInf_iff,
    Set.image_subset_iff, preimage_iUnion]
  refine fun t ht => iInf_le_of_le _ (iInf_le_of_le ht <| ENNReal.tsum_le_tsum fun k => ?_)
  exact iInf_mono fun i => (m i).mono (image_preimage_subset _ _)

/--
theorem `map_iInf` / 定理 `map_iInf`

English:
theorem map_iInf
  given: {ι β} {f : α -> β} (hf : Injective f) (m : ι -> OuterMeasure α)
  proof: by
  refine Eq.trans ?_ (map_comap _ _)
  simp only [comap_iInf, comap_map hf]

中文:
定理 map_iInf
  条件: {ι β} {f : α -> β} (hf : Injective f) (m : ι -> OuterMeasure α)
  证明: by
  refine Eq.trans ?_ (map_comap _ _)
  simp only [comap_iInf, comap_map hf]

Depends on / 依赖: Eq.trans, comap_iInf, comap_map, map_comap
-/
theorem map_iInf {ι β} {f : α -> β} (hf : Injective f) (m : ι -> OuterMeasure α) :
    map f (⨅ i, m i) = restrict (range f) (⨅ i, map f (m i)) := by
  refine Eq.trans ?_ (map_comap _ _)
  simp only [comap_iInf, comap_map hf]

/--
theorem `map_iInf_comap` / 定理 `map_iInf_comap`

English:
theorem map_iInf_comap
  given: {ι β} [Nonempty ι] {f : α -> β} (m : ι -> OuterMeasure β)
  proof: by
  refine (map_iInf_le _ _).antisymm fun s => ?_
  simp only [map_apply, comap_apply, iInf_apply, le_iInf_iff]
  refine fun t ht => iInf_le_of_le (fun n => f '' t n union (range f)ᶜ) (iInf_le_of_le ?_ ?_)
  · rw [← iUnion_union, Set.union_comm, ← inter_subset, ← image_iUnion, ←
      image_preimag

中文:
定理 map_iInf_comap
  条件: {ι β} [Nonempty ι] {f : α -> β} (m : ι -> OuterMeasure β)
  证明: by
  refine (map_iInf_le _ _).antisymm fun s => ?_
  simp only [map_apply, comap_apply, iInf_apply, le_iInf_iff]
  refine fun t ht => iInf_le_of_le (fun n => f '' t n union (range f)ᶜ) (iInf_le_of_le ?_ ?_)
  · rw [← iUnion_union, Set.union_comm, ← inter_subset, ← image_iUnion, ←
      image_preimag

Depends on / 依赖: ENNReal, ENNReal.tsum_le_tsum, Set.union_comm, antisymm, comap_apply, compl_univ, iInf_apply, iInf_le_of_le, iInf_mono, iUnion_union, image_iUnion, image_mono, image_preimage_eq_inter_range, image_subset_iff, inter_subset, le_iInf_iff, map_apply, map_iInf_le, preimage_compl, preimage_range
-/
theorem map_iInf_comap {ι β} [Nonempty ι] {f : α -> β} (m : ι -> OuterMeasure β) :
    map f (⨅ i, comap f (m i)) = ⨅ i, map f (comap f (m i)) := by
  refine (map_iInf_le _ _).antisymm fun s => ?_
  simp only [map_apply, comap_apply, iInf_apply, le_iInf_iff]
  refine fun t ht => iInf_le_of_le (fun n => f '' t n union (range f)ᶜ) (iInf_le_of_le ?_ ?_)
  · rw [← iUnion_union, Set.union_comm, ← inter_subset, ← image_iUnion, ←
      image_preimage_eq_inter_range]
    exact image_mono ht
  · refine ENNReal.tsum_le_tsum fun n => iInf_mono fun i => (m i).mono ?_
    simpa only [preimage_union, preimage_compl, preimage_range, compl_univ, union_empty,
      image_subset_iff] using subset_rfl

/--
theorem `map_biInf_comap` / 定理 `map_biInf_comap`

English:
theorem map_biInf_comap
  given: {ι β} {I : Set ι} (hI : I.Nonempty) {f : α -> β} (m : ι -> OuterMeasure β)
  proof: by
  have := hI.to_subtype
  rw [← iInf_subtype'']; rw [← iInf_subtype'']
  exact map_iInf_comap _

中文:
定理 map_biInf_comap
  条件: {ι β} {I : Set ι} (hI : I.Nonempty) {f : α -> β} (m : ι -> OuterMeasure β)
  证明: by
  have := hI.to_subtype
  rw [← iInf_subtype'']; rw [← iInf_subtype'']
  exact map_iInf_comap _

Depends on / 依赖: hI.to_subtype, iInf_subtype, map_iInf_comap, to_subtype
-/
theorem map_biInf_comap {ι β} {I : Set ι} (hI : I.Nonempty) {f : α -> β} (m : ι -> OuterMeasure β) :
    map f (⨅ i in I, comap f (m i)) = ⨅ i in I, map f (comap f (m i)) := by
  have := hI.to_subtype
  rw [← iInf_subtype'']; rw [← iInf_subtype'']
  exact map_iInf_comap _

/--
theorem `restrict_iInf_restrict` / 定理 `restrict_iInf_restrict`

English:
theorem restrict_iInf_restrict
  given: {ι} (s : Set α) (m : ι -> OuterMeasure α)
  proof: calc restrict s (⨅ i, restrict s (m i))
    _ = restrict (range ((↑) : s -> α)) (⨅ i, restrict s (m i)) := by rw [Subtype.range_coe]
    _ = map ((↑) : s -> α) (⨅ i, comap (↑) (m i)) := (map_iInf Subtype.coe_injective _).symm
    _ = restrict s (⨅ i, m i) := congr_arg (map ((↑) : s -> α)) (comap_iIn

中文:
定理 restrict_iInf_restrict
  条件: {ι} (s : Set α) (m : ι -> OuterMeasure α)
  证明: calc restrict s (⨅ i, restrict s (m i))
    _ = restrict (range ((↑) : s -> α)) (⨅ i, restrict s (m i)) := by rw [Subtype.range_coe]
    _ = map ((↑) : s -> α) (⨅ i, comap (↑) (m i)) := (map_iInf Subtype.coe_injective _).symm
    _ = restrict s (⨅ i, m i) := congr_arg (map ((↑) : s -> α)) (comap_iIn

Depends on / 依赖: Subtype, Subtype.coe_injective, Subtype.range_coe, coe_injective, comap_iInf, congr_arg, map_iInf, range_coe, restrict
-/
theorem restrict_iInf_restrict {ι} (s : Set α) (m : ι -> OuterMeasure α) :
    restrict s (⨅ i, restrict s (m i)) = restrict s (⨅ i, m i) :=
  calc restrict s (⨅ i, restrict s (m i))
    _ = restrict (range ((↑) : s -> α)) (⨅ i, restrict s (m i)) := by rw [Subtype.range_coe]
    _ = map ((↑) : s -> α) (⨅ i, comap (↑) (m i)) := (map_iInf Subtype.coe_injective _).symm
    _ = restrict s (⨅ i, m i) := congr_arg (map ((↑) : s -> α)) (comap_iInf _ _).symm

/--
theorem `restrict_iInf` / 定理 `restrict_iInf`

English:
theorem restrict_iInf
  given: {ι} [Nonempty ι] (s : Set α) (m : ι -> OuterMeasure α)
  proof: (congr_arg (map ((↑) : s -> α)) (comap_iInf _ _)).trans (map_iInf_comap _)

中文:
定理 restrict_iInf
  条件: {ι} [Nonempty ι] (s : Set α) (m : ι -> OuterMeasure α)
  证明: (congr_arg (map ((↑) : s -> α)) (comap_iInf _ _)).trans (map_iInf_comap _)

Depends on / 依赖: comap_iInf, congr_arg, map_iInf_comap
-/
theorem restrict_iInf {ι} [Nonempty ι] (s : Set α) (m : ι -> OuterMeasure α) :
    restrict s (⨅ i, m i) = ⨅ i, restrict s (m i) :=
  (congr_arg (map ((↑) : s -> α)) (comap_iInf _ _)).trans (map_iInf_comap _)

/--
theorem `restrict_biInf` / 定理 `restrict_biInf`

English:
theorem restrict_biInf
  given: {ι} {I : Set ι} (hI : I.Nonempty) (s : Set α) (m : ι -> OuterMeasure α)
  proof: by
  have := hI.to_subtype
  rw [← iInf_subtype'']; rw [← iInf_subtype'']
  exact restrict_iInf _ _

中文:
定理 restrict_biInf
  条件: {ι} {I : Set ι} (hI : I.Nonempty) (s : Set α) (m : ι -> OuterMeasure α)
  证明: by
  have := hI.to_subtype
  rw [← iInf_subtype'']; rw [← iInf_subtype'']
  exact restrict_iInf _ _

Depends on / 依赖: hI.to_subtype, iInf_subtype, restrict_iInf, to_subtype
-/
theorem restrict_biInf {ι} {I : Set ι} (hI : I.Nonempty) (s : Set α) (m : ι -> OuterMeasure α) :
    restrict s (⨅ i in I, m i) = ⨅ i in I, restrict s (m i) := by
  have := hI.to_subtype
  rw [← iInf_subtype'']; rw [← iInf_subtype'']
  exact restrict_iInf _ _

/--
theorem `restrict_sInf_eq_sInf_restrict` / 定理 `restrict_sInf_eq_sInf_restrict`

English:
theorem restrict_sInf_eq_sInf_restrict
  given: (m : Set (OuterMeasure α)) {s : Set α} (hm : m.Nonempty)
  proof: by
  simp only [sInf_eq_iInf, restrict_biInf, hm, iInf_image]

中文:
定理 restrict_sInf_eq_sInf_restrict
  条件: (m : Set (OuterMeasure α)) {s : Set α} (hm : m.Nonempty)
  证明: by
  simp only [sInf_eq_iInf, restrict_biInf, hm, iInf_image]

Depends on / 依赖: iInf_image, restrict_biInf, sInf_eq_iInf
-/
theorem restrict_sInf_eq_sInf_restrict (m : Set (OuterMeasure α)) {s : Set α} (hm : m.Nonempty) :
    restrict s (sInf m) = sInf (restrict s '' m) := by
  simp only [sInf_eq_iInf, restrict_biInf, hm, iInf_image]

end sInfGen

end OuterMeasure

end MeasureTheory
