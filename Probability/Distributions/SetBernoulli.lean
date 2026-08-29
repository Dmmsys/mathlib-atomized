/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.HasLaw

import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Product of bernoulli distributions on a set

This file defines the product of bernoulli distributions on a set as a measure on sets.
For a set `u : Set ι` and `p` between `0` and `1`, this is the measure on `Set ι` such that each
`i ∈ u` belongs to the random set with probability `p`, and each `i ∉ u` doesn't belong to it.

## Notation

`setBer(u, p)` is the product of `p`-Bernoulli distributions on `u`.

## TODO

It is painful to convert from `unitInterval` to `ENNReal`. Should we introduce a coercion or
explicit operation (like `unitInterval.toNNReal`, note the lack of dot notation!)?
-/

public section

open MeasureTheory Measure unitInterval
open scoped ENNReal Finset

namespace ProbabilityTheory
variable {ι Ω : Type*} {m : MeasurableSpace Ω} {X Y : Ω -> Set ι} {s u : Set ι} {i j : ι} {p q : I}
  {P : Measure Ω}

variable (u p) in
/-- The product of bernoulli distributions with parameter `p` on the set `u : Set V` is the measure
on `Set V` such that each element of `u` is taken with probability `p`, and the elements outside of
`u` are never taken. -/
@[expose]
/--
Definition of `setBernoulli` / `setBernoulli` 的定义

English:
definition setBernoulli
  signature: : Measure (Set ι)
  body: .comap (fun s i => i in s) infinitePi fun i : ι =>
    toNNReal p • dirac (i in u) + toNNReal (σ p) • dirac False

@[inherit_doc] scoped notation "setBer(" u ", " p ")" => setBernoulli u p

中文:
定义 setBernoulli
  签名: : 测度 (集合 ι)
  定义体: .comap (fun s i => i in s) infinitePi fun i : ι =>
    toNNReal p • dirac (i in u) + toNNReal (σ p) • dirac False

@[inherit_doc] scoped notation "setBer(" u ", " p ")" => setBernoulli u p

Depends on / 依赖: infinitePi, toNNReal
-/
noncomputable def setBernoulli : Measure (Set ι) :=
.comap (fun s i => i in s) infinitePi fun i : ι =>
    toNNReal p • dirac (i in u) + toNNReal (σ p) • dirac False

@[inherit_doc] scoped notation "setBer(" u ", " p ")" => setBernoulli u p

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsProbabilityMeasure setBer(u, p)
  body: MeasurableEquiv.setOfPred.symm.measurableEmbedding.isProbabilityMeasure_comap
    .of_forall fun P => ⟨{i | P i}, rfl⟩

中文:
实例 :
  签名: 是概率测度 setBer(u, p)
  定义体: MeasurableEquiv.setOfPred.symm.measurableEmbedding.isProbabilityMeasure_comap
    .of_forall fun P => ⟨{i | P i}, rfl⟩

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.setOfPred.symm.measurableEmbedding.isProbabilityMeasure_comap, isProbabilityMeasure_comap, measurableEmbedding, of_forall, setOfPred
-/
instance : IsProbabilityMeasure setBer(u, p) :=
MeasurableEquiv.setOfPred.symm.measurableEmbedding.isProbabilityMeasure_comap
    .of_forall fun P => ⟨{i | P i}, rfl⟩

variable (u p) in
/--
lemma `setBernoulli_eq_map` / 引理 `setBernoulli_eq_map`

English:
lemma setBernoulli_eq_map
  proof: MeasurableEquiv.setOfPred.comap_symm

中文:
引理 setBernoulli_eq_map
  证明: MeasurableEquiv.setOfPred.comap_symm

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.setOfPred.comap_symm, comap_symm, setOfPred
-/
lemma setBernoulli_eq_map :
    setBer(u, p) = .map (fun p : ι -> Prop => {i | p i})
      (infinitePi fun i : ι => toNNReal p • dirac (i in u) + toNNReal (σ p) • dirac False) :=
  MeasurableEquiv.setOfPred.comap_symm

/--
lemma `setBernoulli_apply` / 引理 `setBernoulli_apply`

English:
lemma setBernoulli_apply
  given: (S : Set (Set ι))
  proof: MeasurableEquiv.setOfPred.symm.measurableEmbedding.comap_apply ..

中文:
引理 setBernoulli_apply
  条件: (S : 集合 (集合 ι))
  证明: MeasurableEquiv.setOfPred.symm.measurableEmbedding.comap_apply ..

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.setOfPred.symm.measurableEmbedding.comap_apply, comap_apply, measurableEmbedding, setOfPred
-/
lemma setBernoulli_apply (S : Set (Set ι)) :
    setBer(u, p) S = (infinitePi fun i => toNNReal p • dirac (i in u) + toNNReal (σ p) • dirac False)
      ((fun t i => i in t) '' S) := MeasurableEquiv.setOfPred.symm.measurableEmbedding.comap_apply ..

/--
lemma `setBernoulli_apply'` / 引理 `setBernoulli_apply'`

English:
lemma setBernoulli_apply'
  given: (S : Set (Set ι))
  proof: MeasurableEquiv.setOfPred.symm.comap_apply ..

中文:
引理 setBernoulli_apply'
  条件: (S : 集合 (集合 ι))
  证明: MeasurableEquiv.setOfPred.symm.comap_apply ..

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.setOfPred.symm.comap_apply, comap_apply, setOfPred
-/
lemma setBernoulli_apply' (S : Set (Set ι)) :
    setBer(u, p) S = (infinitePi fun i => toNNReal p • dirac (i in u) + toNNReal (σ p) • dirac False)
      ((fun p => {i | p i}) ⁻¹' S) := MeasurableEquiv.setOfPred.symm.comap_apply ..

variable (u) in
/--
lemma `setBernoulli_zero` / 引理 `setBernoulli_zero`

English:
lemma setBernoulli_zero
  statement: setBer(u, 0) = dirac ∅
  proof: by simp [setBernoulli_eq_map]

中文:
引理 setBernoulli_zero
  结论: setBer(u, 0) = dirac ∅
  证明: by simp [setBernoulli_eq_map]
-/
@[simp] lemma setBernoulli_zero : setBer(u, 0) = dirac ∅ := by simp [setBernoulli_eq_map]

variable (u) in
/--
lemma `setBernoulli_one` / 引理 `setBernoulli_one`

English:
lemma setBernoulli_one
  statement: setBer(u, 1) = dirac u
  proof: by simp [setBernoulli_eq_map]

中文:
引理 setBernoulli_one
  结论: setBer(u, 1) = dirac u
  证明: by simp [setBernoulli_eq_map]
-/
@[simp] lemma setBernoulli_one : setBer(u, 1) = dirac u := by simp [setBernoulli_eq_map]

section Countable
variable [Countable ι]

/--
lemma `setBernoulli_ae_subset` / 引理 `setBernoulli_ae_subset`

English:
lemma setBernoulli_ae_subset
  statement: forallᵐ s ∂setBer(u, p), s subseteq u
  proof: by
  simp only [Filter.Eventually, mem_ae_iff, Set.compl_ofPred, Set.not_subset_iff_exists_mem_notMem,
    Set.ofPred_exists, Set.ofPred_and, measure_iUnion_null_iff]
  rintro i
  by_cases hi : i in u
  · simp [*]
  calc
    setBer(u, p) ({s | i in s} inter {s | i ∉ u})
    _ = setBer(u, p) {s | i in s} := by simp [hi]
    _ = infinitePi (fun i => toNNReal p • dirac (i in u) + toNNReal (σ p) • dirac False)
          (cylinder {i} {fun _ => True}) := by
      rw [setBernoulli_apply']; congr!; ext; simp [funext_iff]
    _ = 0 := by simp [infinitePi_cylinder, hi]

@[simp]

中文:
引理 setBernoulli_ae_subset
  结论: 对任意ᵐ s ∂setBer(u, p), s subseteq u
  证明: by
  simp only [Filter.Eventually, mem_ae_iff, Set.compl_ofPred, Set.not_subset_iff_exists_mem_notMem,
    Set.ofPred_exists, Set.ofPred_and, measure_iUnion_null_iff]
  rintro i
  by_cases hi : i in u
  · simp [*]
  calc
    setBer(u, p) ({s | i in s} inter {s | i ∉ u})
    _ = setBer(u, p) {s | i in s} := by simp [hi]
    _ = infinitePi (fun i => toNNReal p • dirac (i in u) + toNNReal (σ p) • dirac False)
          (cylinder {i} {fun _ => True}) := by
      rw [setBernoulli_apply']; congr!; ext; simp [funext_iff]
    _ = 0 := by simp [infinitePi_cylinder, hi]

@[simp]

Depends on / 依赖: Eventually, Filter, Filter.Eventually, Set.compl_ofPred, Set.not_subset_iff_exists_mem_notMem, Set.ofPred_and, Set.ofPred_exists, compl_ofPred, cylinder, funext_iff, infinitePi, measure_iUnion_null_iff, mem_ae_iff, not_subset_iff_exists_mem_notMem, ofPred_and, ofPred_exists, setBer, setBernoulli_apply, toNNReal
-/
lemma setBernoulli_ae_subset : forallᵐ s ∂setBer(u, p), s subseteq u := by
  simp only [Filter.Eventually, mem_ae_iff, Set.compl_ofPred, Set.not_subset_iff_exists_mem_notMem,
    Set.ofPred_exists, Set.ofPred_and, measure_iUnion_null_iff]
  rintro i
  by_cases hi : i in u
  · simp [*]
  calc
    setBer(u, p) ({s | i in s} inter {s | i ∉ u})
    _ = setBer(u, p) {s | i in s} := by simp [hi]
    _ = infinitePi (fun i => toNNReal p • dirac (i in u) + toNNReal (σ p) • dirac False)
          (cylinder {i} {fun _ => True}) := by
      rw [setBernoulli_apply']; congr!; ext; simp [funext_iff]
    _ = 0 := by simp [infinitePi_cylinder, hi]

@[simp]
/--
lemma `setBernoulli_singleton_of_not_subset` / 引理 `setBernoulli_singleton_of_not_subset`

English:
lemma setBernoulli_singleton_of_not_subset
  given: {s : Set ι} (p : I) (hs : ¬ s subseteq u)
  proof: Measure.mono_null (by simpa) setBernoulli_ae_subset

中文:
引理 setBernoulli_singleton_of_not_subset
  条件: {s : 集合 ι} (p : I) (hs : ¬ s subseteq u)
  证明: Measure.mono_null (by simpa) setBernoulli_ae_subset

Depends on / 依赖: Measure, Measure.mono_null, mono_null, setBernoulli_ae_subset
-/
lemma setBernoulli_singleton_of_not_subset {s : Set ι} (p : I) (hs : ¬ s subseteq u) :
    setBer(u, p) {s} = 0 :=
  Measure.mono_null (by simpa) setBernoulli_ae_subset

/--
lemma `setBernoulli_apply_eq_apply_subsets` / 引理 `setBernoulli_apply_eq_apply_subsets`

English:
lemma setBernoulli_apply_eq_apply_subsets
  given: (u : Set ι) (p : I) (S : Set (Set ι))
  proof: by
  apply (measure_eq_measure_of_null_sdiff (by grind) ?_).symm
  exact Measure.mono_null (by grind) setBernoulli_ae_subset

中文:
引理 setBernoulli_apply_eq_apply_subsets
  条件: (u : 集合 ι) (p : I) (S : 集合 (集合 ι))
  证明: by
  apply (measure_eq_measure_of_null_sdiff (by grind) ?_).symm
  exact Measure.mono_null (by grind) setBernoulli_ae_subset

Depends on / 依赖: Measure, Measure.mono_null, measure_eq_measure_of_null_sdiff, mono_null, setBernoulli_ae_subset
-/
lemma setBernoulli_apply_eq_apply_subsets (u : Set ι) (p : I) (S : Set (Set ι)) :
    setBer(u, p) S = setBer(u, p) { s in S | s subseteq u} := by
  apply (measure_eq_measure_of_null_sdiff (by grind) ?_).symm
  exact Measure.mono_null (by grind) setBernoulli_ae_subset

/--
lemma `map_ncard_setBernoulli_apply` / 引理 `map_ncard_setBernoulli_apply`

English:
lemma map_ncard_setBernoulli_apply
  given: (u : Set ι) (p : I) (s : Set Nat)
  proof: by
  rw [map_apply (by fun_prop) .of_discrete]; rw [setBernoulli_apply_eq_apply_subsets]
  simp [And.comm]

中文:
引理 map_ncard_setBernoulli_apply
  条件: (u : 集合 ι) (p : I) (s : 集合 自然数)
  证明: by
  rw [map_apply (by fun_prop) .of_discrete]; rw [setBernoulli_apply_eq_apply_subsets]
  simp [And.comm]

Depends on / 依赖: And.comm, fun_prop, map_apply, of_discrete, setBernoulli_apply_eq_apply_subsets
-/
lemma map_ncard_setBernoulli_apply (u : Set ι) (p : I) (s : Set Nat) :
    (setBer(u, p).map Set.ncard) s = setBer(u, p) {t subseteq u | t.ncard in s} := by
  rw [map_apply (by fun_prop) .of_discrete]; rw [setBernoulli_apply_eq_apply_subsets]
  simp [And.comm]

variable (p) in
/--
lemma `setBernoulli_singleton` / 引理 `setBernoulli_singleton`

English:
lemma setBernoulli_singleton
  given: (hsu : s subseteq u) (hu : u.Finite)
  proof: by
  classical
  lift u to Finset ι using hu
  calc
    setBer(u, p) {s}
    _ = ∏' i, ((if i in u ↔ i in s then (toNNReal p : Real>=0∞) else 0) +
          if i in s then 0 else (toNNReal (σ p) : Real>=0∞)) := by
      simp [setBernoulli_apply, Set.image_singleton, Set.indicator]
    _ = ∏ i in u, (if i in s then (toNNReal p : Real>=0∞) else (toNNReal (σ p) : Real>=0∞)) := by
      rw [tprod_eq_prod]; rw [Finset.prod_congr rfl] <;>
        simp +contextual [ite_add_ite, mt (@hsu _), ← ENNReal.coe_add]
    _ = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (↑u \ s).ncard := by
      simp [Finset.prod_ite, ← Set.ncard_coe_finset, Set.ofPred_and,
        Set.inter_eq_right.2 hsu, ← Set.compl_ofPred, Set.sdiff_eq_compl_inter, Set.inter_comm]

@[simp]

中文:
引理 setBernoulli_singleton
  条件: (hsu : s subseteq u) (hu : u.有限)
  证明: by
  classical
  lift u to Finset ι using hu
  calc
    setBer(u, p) {s}
    _ = ∏' i, ((if i in u ↔ i in s then (toNNReal p : Real>=0∞) else 0) +
          if i in s then 0 else (toNNReal (σ p) : Real>=0∞)) := by
      simp [setBernoulli_apply, Set.image_singleton, Set.indicator]
    _ = ∏ i in u, (if i in s then (toNNReal p : Real>=0∞) else (toNNReal (σ p) : Real>=0∞)) := by
      rw [tprod_eq_prod]; rw [Finset.prod_congr rfl] <;>
        simp +contextual [ite_add_ite, mt (@hsu _), ← ENNReal.coe_add]
    _ = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (↑u \ s).ncard := by
      simp [Finset.prod_ite, ← Set.ncard_coe_finset, Set.ofPred_and,
        Set.inter_eq_right.2 hsu, ← Set.compl_ofPred, Set.sdiff_eq_compl_inter, Set.inter_comm]

@[simp]
-/
@[simp] lemma setBernoulli_singleton (hsu : s subseteq u) (hu : u.Finite) :
    setBer(u, p) {s} = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (u \ s).ncard := by
  classical
  lift u to Finset ι using hu
  calc
    setBer(u, p) {s}
    _ = ∏' i, ((if i in u ↔ i in s then (toNNReal p : Real>=0∞) else 0) +
          if i in s then 0 else (toNNReal (σ p) : Real>=0∞)) := by
      simp [setBernoulli_apply, Set.image_singleton, Set.indicator]
    _ = ∏ i in u, (if i in s then (toNNReal p : Real>=0∞) else (toNNReal (σ p) : Real>=0∞)) := by
      rw [tprod_eq_prod]; rw [Finset.prod_congr rfl] <;>
        simp +contextual [ite_add_ite, mt (@hsu _), ← ENNReal.coe_add]
    _ = toNNReal p ^ s.ncard * toNNReal (σ p) ^ (↑u \ s).ncard := by
      simp [Finset.prod_ite, ← Set.ncard_coe_finset, Set.ofPred_and,
        Set.inter_eq_right.2 hsu, ← Set.compl_ofPred, Set.sdiff_eq_compl_inter, Set.inter_comm]

@[simp]
/--
lemma `setBernoulli_real_singleton` / 引理 `setBernoulli_real_singleton`

English:
lemma setBernoulli_real_singleton
  given: (p : I) (hsu : s subseteq u) (hu : u.Finite)
  proof: by
  simp [measureReal_def, setBernoulli_singleton p hsu hu]

中文:
引理 setBernoulli_real_singleton
  条件: (p : I) (hsu : s subseteq u) (hu : u.有限)
  证明: by
  simp [measureReal_def, setBernoulli_singleton p hsu hu]

Depends on / 依赖: measureReal_def, setBernoulli_singleton
-/
lemma setBernoulli_real_singleton (p : I) (hsu : s subseteq u) (hu : u.Finite) :
    setBer(u, p).real {s} = p ^ s.ncard * (1 - p : Real) ^ (u \ s).ncard := by
  simp [measureReal_def, setBernoulli_singleton p hsu hu]

/--
lemma `map_ncard_setBernoulli_real_singleton` / 引理 `map_ncard_setBernoulli_real_singleton`

English:
lemma map_ncard_setBernoulli_real_singleton
  given: {u : Set ι} (hu : u.Finite) (p : I) (k : Nat)
  proof: by
  have : {s subseteq u | s.ncard in ({k} : Set Nat)}.Finite := hu.finite_subsets.subset (by grind)
  rw [measureReal_def]; rw [map_ncard_setBernoulli_apply]; rw [← measureReal_def]; rw [← Set.biUnion_of_singleton (Set.ofPred _)]
  simp_rw [← this.mem_toFinset]
  rw [measureReal_biUnion_finset (by simp) (by simp)]
  have h1 s (hs : s in this.toFinset) :
      setBer(u, p).real {s} = p ^ k * (1 - p) ^ (u.ncard - k) := by
    simp only [Set.mem_singleton_iff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hs
    rw [setBernoulli_real_singleton _ hs.1 hu]; rw [Set.ncard_sdiff' hs.1 hu]; rw [hs.2]
  rw [Finset.sum_congr rfl h1]; rw [Finset.sum_const]; rw [nsmul_eq_mul]; rw [mul_assoc]; rw [← Set.ncard_eq_toFinset_card _ _]
  simp [Set.ncard_powerset_ncard, hu]

中文:
引理 map_ncard_setBernoulli_real_singleton
  条件: {u : 集合 ι} (hu : u.有限) (p : I) (k : 自然数)
  证明: by
  have : {s subseteq u | s.ncard in ({k} : Set Nat)}.Finite := hu.finite_subsets.subset (by grind)
  rw [measureReal_def]; rw [map_ncard_setBernoulli_apply]; rw [← measureReal_def]; rw [← Set.biUnion_of_singleton (Set.ofPred _)]
  simp_rw [← this.mem_toFinset]
  rw [measureReal_biUnion_finset (by simp) (by simp)]
  have h1 s (hs : s in this.toFinset) :
      setBer(u, p).real {s} = p ^ k * (1 - p) ^ (u.ncard - k) := by
    simp only [Set.mem_singleton_iff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hs
    rw [setBernoulli_real_singleton _ hs.1 hu]; rw [Set.ncard_sdiff' hs.1 hu]; rw [hs.2]
  rw [Finset.sum_congr rfl h1]; rw [Finset.sum_const]; rw [nsmul_eq_mul]; rw [mul_assoc]; rw [← Set.ncard_eq_toFinset_card _ _]
  simp [Set.ncard_powerset_ncard, hu]

Depends on / 依赖: Finite, Set.Finite.mem_toFinset, Set.biUnion_of_singleton, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.ofPred, biUnion_of_singleton, finite_subsets, hu.finite_subsets.subset, map_ncard_setBernoulli_apply, measureReal_biUnion_finset, measureReal_def, mem_ofPred_eq, mem_singleton_iff, mem_toFinset, ofPred, s.ncard, setBer, simp_rw, subset
-/
lemma map_ncard_setBernoulli_real_singleton {u : Set ι} (hu : u.Finite) (p : I) (k : Nat) :
    (setBer(u, p).map Set.ncard).real {k} =
      (u.ncard.choose k) * p ^ k * (1 - p) ^ (u.ncard - k) := by
  have : {s subseteq u | s.ncard in ({k} : Set Nat)}.Finite := hu.finite_subsets.subset (by grind)
  rw [measureReal_def]; rw [map_ncard_setBernoulli_apply]; rw [← measureReal_def]; rw [← Set.biUnion_of_singleton (Set.ofPred _)]
  simp_rw [← this.mem_toFinset]
  rw [measureReal_biUnion_finset (by simp) (by simp)]
  have h1 s (hs : s in this.toFinset) :
      setBer(u, p).real {s} = p ^ k * (1 - p) ^ (u.ncard - k) := by
    simp only [Set.mem_singleton_iff, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hs
    rw [setBernoulli_real_singleton _ hs.1 hu]; rw [Set.ncard_sdiff' hs.1 hu]; rw [hs.2]
  rw [Finset.sum_congr rfl h1]; rw [Finset.sum_const]; rw [nsmul_eq_mul]; rw [mul_assoc]; rw [← Set.ncard_eq_toFinset_card _ _]
  simp [Set.ncard_powerset_ncard, hu]

/--
lemma `map_ncard_setBernoulli_singleton` / 引理 `map_ncard_setBernoulli_singleton`

English:
lemma map_ncard_setBernoulli_singleton
  given: {u : Set ι} (hu : u.Finite) (p : I) (k : Nat)
  proof: by
  rw [← ENNReal.ofReal_toReal (a := (Measure.map _ _) _) (by simp)]; rw [← measureReal_def]; rw [map_ncard_setBernoulli_real_singleton hu]

@[simp]

中文:
引理 map_ncard_setBernoulli_singleton
  条件: {u : 集合 ι} (hu : u.有限) (p : I) (k : 自然数)
  证明: by
  rw [← ENNReal.ofReal_toReal (a := (Measure.map _ _) _) (by simp)]; rw [← measureReal_def]; rw [map_ncard_setBernoulli_real_singleton hu]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal_toReal, Measure, Measure.map, map_ncard_setBernoulli_real_singleton, measureReal_def, ofReal_toReal
-/
lemma map_ncard_setBernoulli_singleton {u : Set ι} (hu : u.Finite) (p : I) (k : Nat) :
    (setBer(u, p).map Set.ncard) {k} =
      ENNReal.ofReal ((u.ncard.choose k) * p ^ k * (1 - p) ^ (u.ncard - k)) := by
  rw [← ENNReal.ofReal_toReal (a := (Measure.map _ _) _) (by simp)]; rw [← measureReal_def]; rw [map_ncard_setBernoulli_real_singleton hu]

@[simp]
/--
lemma `setBernoulli_empty` / 引理 `setBernoulli_empty`

English:
lemma setBernoulli_empty
  statement: setBer((∅ : Set ι), p) = dirac ∅
  proof: by
  ext s hs
  rw [setBernoulli_apply_eq_apply_subsets]
  by_cases h : ∅ in s
  · have : {t | t in s ∧ t subseteq ∅} = {∅} := by grind
    simp_all
  · have : {t | t in s ∧ t subseteq ∅} = ∅ := by grind
    rw [this]
    simp_all

中文:
引理 setBernoulli_empty
  结论: setBer((∅ : 集合 ι), p) = dirac ∅
  证明: by
  ext s hs
  rw [setBernoulli_apply_eq_apply_subsets]
  by_cases h : ∅ in s
  · have : {t | t in s ∧ t subseteq ∅} = {∅} := by grind
    simp_all
  · have : {t | t in s ∧ t subseteq ∅} = ∅ := by grind
    rw [this]
    simp_all

Depends on / 依赖: setBernoulli_apply_eq_apply_subsets, subseteq
-/
lemma setBernoulli_empty : setBer((∅ : Set ι), p) = dirac ∅ := by
  ext s hs
  rw [setBernoulli_apply_eq_apply_subsets]
  by_cases h : ∅ in s
  · have : {t | t in s ∧ t subseteq ∅} = {∅} := by grind
    simp_all
  · have : {t | t in s ∧ t subseteq ∅} = ∅ := by grind
    rw [this]
    simp_all

end Countable

/-! ### Bernoulli random variables -/

variable (X u p P) in
/--
Definition of `IsSetBernoulli` / `IsSetBernoulli` 的定义

English:
abbreviation IsSetBernoulli
  signature: : Prop
  body: HasLaw X setBer(u, p) P

中文:
缩写 IsSetBernoulli
  签名: : 命题
  定义体: HasLaw X setBer(u, p) P

Depends on / 依赖: HasLaw, setBer
-/
abbrev IsSetBernoulli : Prop := HasLaw X setBer(u, p) P

/--
lemma `isSetBernoulli_congr` / 引理 `isSetBernoulli_congr`

English:
lemma isSetBernoulli_congr
  given: (hXY : X =ᵐ[P] Y)
  statement: IsSetBernoulli X u p P ↔ IsSetBernoulli Y u p P
  proof: hasLaw_congr hXY

中文:
引理 isSetBernoulli_congr
  条件: (hXY : X =ᵐ[P] Y)
  结论: IsSetBernoulli X u p P ↔ IsSetBernoulli Y u p P
  证明: hasLaw_congr hXY

Depends on / 依赖: hasLaw_congr
-/
lemma isSetBernoulli_congr (hXY : X =ᵐ[P] Y) : IsSetBernoulli X u p P ↔ IsSetBernoulli Y u p P :=
  hasLaw_congr hXY

variable [Countable ι]

/--
lemma `IsSetBernoulli.ae_subset` / 引理 `IsSetBernoulli.ae_subset`

English:
lemma IsSetBernoulli.ae_subset
  given: (hX : IsSetBernoulli X u p P)
  statement: forallᵐ ω ∂P, X ω subseteq u
  proof: (hX.ae_iff <| by fun_prop).2 setBernoulli_ae_subset

中文:
引理 IsSetBernoulli.ae_subset
  条件: (hX : IsSetBernoulli X u p P)
  结论: 对任意ᵐ ω ∂P, X ω subseteq u
  证明: (hX.ae_iff <| by fun_prop).2 setBernoulli_ae_subset

Depends on / 依赖: ae_iff, fun_prop, hX.ae_iff, setBernoulli_ae_subset
-/
lemma IsSetBernoulli.ae_subset (hX : IsSetBernoulli X u p P) : forallᵐ ω ∂P, X ω subseteq u :=
  (hX.ae_iff <| by fun_prop).2 setBernoulli_ae_subset

end ProbabilityTheory
