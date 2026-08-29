/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Absolutely Continuous Functions

This file defines absolutely continuous functions on a closed interval `uIcc a b` and proves some
basic properties about absolutely continuous functions.

A function `f` is *absolutely continuous* on `uIcc a b` if for any `ε > 0`, there is `δ > 0` such
that for any finite disjoint collection of intervals `uIoc (a i) (b i)` for `i < n` where `a i`,
`b i` are all in `uIcc a b` for `i < n`, if `∑ i ∈ range n, dist (a i) (b i) < δ`, then
`∑ i ∈ range n, dist (f (a i)) (f (b i)) < ε`.

We give a filter version of the definition of absolutely continuous functions in
`AbsolutelyContinuousOnInterval` based on `AbsolutelyContinuousOnInterval.totalLengthFilter`
and `AbsolutelyContinuousOnInterval.disjWithin` and prove its equivalence with the `ε`-`δ`
definition in `absolutelyContinuousOnInterval_iff`.

We use the filter version to prove that absolutely continuous functions are closed under
* addition - `AbsolutelyContinuousOnInterval.add`;
* negation - `AbsolutelyContinuousOnInterval.neg`;
* subtraction - `AbsolutelyContinuousOnInterval.sub`;
* scalar multiplication - `AbsolutelyContinuousOnInterval.const_smul`,
  `AbsolutelyContinuousOnInterval.const_mul`;
* multiplication - `AbsolutelyContinuousOnInterval.smul`,
  `AbsolutelyContinuousOnInterval.mul`;

and that absolutely continuous implies uniformly continuous in
`AbsolutelyContinuousOnInterval.uniformContinuousOn`.

We use the `ε`-`δ` definition to prove that
* Lipschitz continuous functions are absolutely continuous -
  `LipschitzOnWith.absolutelyContinuousOnInterval`;
* absolutely continuous functions have bounded variation -
  `AbsolutelyContinuousOnInterval.boundedVariationOn`.

We conclude that
* absolutely continuous functions are a.e. differentiable -
  `AbsolutelyContinuousOnInterval.ae_differentiableAt`;
* if `f` is integrable on `uIcc a b`, then for any `c` in `uIcc a b`, `fun x ↦ ∫ v in c..x, f v`
  is absolutely continuous on `uIcc a b` -
  `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`.

## Tags
absolutely continuous
-/

@[expose] public section

variable {X F : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup F]

open Set Filter Function MeasureTheory

open scoped Topology NNReal

namespace AbsolutelyContinuousOnInterval

/--
Definition of `totalLengthFilter` / `totalLengthFilter` 的定义

English:
definition totalLengthFilter
  signature: : Filter (Nat × (Nat -> X × X))
  body: Filter.comap
  (fun E => ∑ i in Finset.range E.1, dist (E.2 i).1 (E.2 i).2) (𝓝 0)

中文:
定义 totalLengthFilter
  签名: : Filter (自然数 × (自然数 -> X × X))
  定义体: Filter.comap
  (fun E => ∑ i in Finset.range E.1, dist (E.2 i).1 (E.2 i).2) (𝓝 0)

Depends on / 依赖: Filter, Filter.comap
-/
def totalLengthFilter : Filter (Nat × (Nat -> X × X)) := Filter.comap
  (fun E => ∑ i in Finset.range E.1, dist (E.2 i).1 (E.2 i).2) (𝓝 0)

/--
lemma `hasBasis_totalLengthFilter` / 引理 `hasBasis_totalLengthFilter`

English:
lemma hasBasis_totalLengthFilter
  statement: totalLengthFilter.HasBasis (fun (ε : Real) => 0 < ε)
  proof: by
  convert! Filter.HasBasis.comap (α := Real) _ (nhds_basis_Ioo_pos _) using 1
  ext ε E
  simp only [mem_ofPred_eq, zero_sub, zero_add, mem_preimage, mem_Ioo, iff_and_self]
  suffices 0 <= ∑ i in Finset.range E.1, dist (E.2 i).1 (E.2 i).2 by grind
  exact Finset.sum_nonneg (fun _ _ => dist_nonneg

中文:
引理 hasBasis_totalLengthFilter
  结论: totalLengthFilter.HasBasis (fun (ε : 实数) => 0 < ε)
  证明: by
  convert! Filter.HasBasis.comap (α := Real) _ (nhds_basis_Ioo_pos _) using 1
  ext ε E
  simp only [mem_ofPred_eq, zero_sub, zero_add, mem_preimage, mem_Ioo, iff_and_self]
  suffices 0 <= ∑ i in Finset.range E.1, dist (E.2 i).1 (E.2 i).2 by grind
  exact Finset.sum_nonneg (fun _ _ => dist_nonneg

Depends on / 依赖: Filter, Filter.HasBasis.comap, Finset, Finset.range, Finset.sum_nonneg, HasBasis, convert, dist_nonneg, iff_and_self, mem_Ioo, mem_ofPred_eq, mem_preimage, nhds_basis_Ioo_pos, sum_nonneg, zero_add, zero_sub
-/
lemma hasBasis_totalLengthFilter : totalLengthFilter.HasBasis (fun (ε : Real) => 0 < ε)
    (fun (ε : Real) =>
      {E : Nat × (Nat -> X × X) | ∑ i in Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < ε}) := by
  convert! Filter.HasBasis.comap (α := Real) _ (nhds_basis_Ioo_pos _) using 1
  ext ε E
  simp only [mem_ofPred_eq, zero_sub, zero_add, mem_preimage, mem_Ioo, iff_and_self]
  suffices 0 <= ∑ i in Finset.range E.1, dist (E.2 i).1 (E.2 i).2 by grind
  exact Finset.sum_nonneg (fun _ _ => dist_nonneg)

/--
Definition of `disjWithin` / `disjWithin` 的定义

English:
definition disjWithin
  signature: (a b : Real)
  body: {E : Nat × (Nat -> Real × Real) |
  (forall i in Finset.range E.1, (E.2 i).1 in uIcc a b ∧ (E.2 i).2 in uIcc a b) ∧
  Set.PairwiseDisjoint (Finset.range E.1) (fun i => uIoc (E.2 i).1 (E.2 i).2)}

中文:
定义 disjWithin
  签名: (a b : 实数)
  定义体: {E : Nat × (Nat -> Real × Real) |
  (forall i in Finset.range E.1, (E.2 i).1 in uIcc a b ∧ (E.2 i).2 in uIcc a b) ∧
  Set.PairwiseDisjoint (Finset.range E.1) (fun i => uIoc (E.2 i).1 (E.2 i).2)}

Depends on / 依赖: _conj, _neg_left, div_neg, exp_conj, map_ofNat, neg_div
-/
def disjWithin (a b : Real) := {E : Nat × (Nat -> Real × Real) |
  (forall i in Finset.range E.1, (E.2 i).1 in uIcc a b ∧ (E.2 i).2 in uIcc a b) ∧
  Set.PairwiseDisjoint (Finset.range E.1) (fun i => uIoc (E.2 i).1 (E.2 i).2)}

/--
lemma `disjWithin_comm` / 引理 `disjWithin_comm`

English:
lemma disjWithin_comm
  given: (a b : Real)
  statement: disjWithin a b = disjWithin b a
  proof: by
  rw [disjWithin]; rw [disjWithin]; rw [uIcc_comm]

中文:
引理 disjWithin_comm
  条件: (a b : 实数)
  结论: disjWithin a b = disjWithin b a
  证明: by
  rw [disjWithin]; rw [disjWithin]; rw [uIcc_comm]

Depends on / 依赖: _add_left, add_mul, disjWithin, generalize, one_mul, uIcc_comm
-/
lemma disjWithin_comm (a b : Real) : disjWithin a b = disjWithin b a := by
  rw [disjWithin]; rw [disjWithin]; rw [uIcc_comm]

/--
lemma `disjWithin_mono` / 引理 `disjWithin_mono`

English:
lemma disjWithin_mono
  given: {a b c d : Real} (habcd : uIcc c d subseteq uIcc a b)
  proof: by
  grind [disjWithin]

中文:
引理 disjWithin_mono
  条件: {a b c d : 实数} (habcd : uIcc c d subseteq uIcc a b)
  证明: by
  grind [disjWithin]

Depends on / 依赖: _neg_left, disjWithin, neg_add, neg_add_rev, neg_div
-/
lemma disjWithin_mono {a b c d : Real} (habcd : uIcc c d subseteq uIcc a b) :
    disjWithin c d subseteq disjWithin a b := by
  grind [disjWithin]

/--
lemma `uIoc_subset_of_mem_disjWithin` / 引理 `uIoc_subset_of_mem_disjWithin`

English:
lemma uIoc_subset_of_mem_disjWithin
  statement: {a b : Real} {n : Nat} {I : Nat -> Real × Real}
  proof: by
  simp only [disjWithin, Finset.mem_range, mem_ofPred_eq, uIcc, mem_Icc] at hnI
  grind

中文:
引理 uIoc_subset_of_mem_disjWithin
  结论: {a b : 实数} {n : 自然数} {I : 自然数 -> 实数 × 实数}
  证明: by
  simp only [disjWithin, Finset.mem_range, mem_ofPred_eq, uIcc, mem_Icc] at hnI
  grind

Depends on / 依赖: Finset, Finset.mem_range, disjWithin, mem_Icc, mem_ofPred_eq, mem_range
-/
lemma uIoc_subset_of_mem_disjWithin {a b : Real} {n : Nat} {I : Nat -> Real × Real}
    (hnI : (n, I) in disjWithin a b) {i : Nat} (hi : i < n) : uIoc (I i).1 (I i).2 subseteq uIoc a b := by
  simp only [disjWithin, Finset.mem_range, mem_ofPred_eq, uIcc, mem_Icc] at hnI
  grind

/--
lemma `biUnion_uIoc_subset_of_mem_disjWithin` / 引理 `biUnion_uIoc_subset_of_mem_disjWithin`

English:
lemma biUnion_uIoc_subset_of_mem_disjWithin
  statement: {a b : Real} {n : Nat} {I : Nat -> Real × Real}
  proof: by
  simp only [iUnion_subset_iff, Finset.mem_range]
  exact fun i hi => uIoc_subset_of_mem_disjWithin hnI hi

中文:
引理 biUnion_uIoc_subset_of_mem_disjWithin
  结论: {a b : 实数} {n : 自然数} {I : 自然数 -> 实数 × 实数}
  证明: by
  simp only [iUnion_subset_iff, Finset.mem_range]
  exact fun i hi => uIoc_subset_of_mem_disjWithin hnI hi

Depends on / 依赖: Finset, Finset.mem_range, iUnion_subset_iff, mem_range, uIoc_subset_of_mem_disjWithin
-/
lemma biUnion_uIoc_subset_of_mem_disjWithin {a b : Real} {n : Nat} {I : Nat -> Real × Real}
    (hnI : (n, I) in disjWithin a b) :
    (⋃ i in Finset.range n, uIoc (I i).1 (I i).2) subseteq uIoc a b := by
  simp only [iUnion_subset_iff, Finset.mem_range]
  exact fun i hi => uIoc_subset_of_mem_disjWithin hnI hi

/--
lemma `tendsto_volume_totalLengthFilter_nhds_zero` / 引理 `tendsto_volume_totalLengthFilter_nhds_zero`

English:
lemma tendsto_volume_totalLengthFilter_nhds_zero
  proof: by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun E => ENNReal.ofReal (∑ i in Finset.range E.1, (dist (E.2 i).1 (E.2 i).2)))
  · convert! ENNReal.tendsto_ofReal (Filter.tendsto_comap)
    simp
  · intro; simp
  · intro E
    simp only
    grw [measure_biUnion_fins

中文:
引理 tendsto_volume_totalLengthFilter_nhds_zero
  证明: by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun E => ENNReal.ofReal (∑ i in Finset.range E.1, (dist (E.2 i).1 (E.2 i).2)))
  · convert! ENNReal.tendsto_ofReal (Filter.tendsto_comap)
    simp
  · intro; simp
  · intro E
    simp only
    grw [measure_biUnion_fins

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.ofReal_sum_of_nonneg, ENNReal.tendsto_ofReal, Eq.le, Filter, Filter.tendsto_comap, Finset, Finset.range, Finset.sum_congr, Real.dist_eq, convert, dist_eq, dist_nonneg, max_sub_min_eq_abs, measure_biUnion_finset_le, ofReal, ofReal_sum_of_nonneg, sum_congr, tendsto_comap
-/
lemma tendsto_volume_totalLengthFilter_nhds_zero :
    Tendsto (fun E : Nat × (Nat -> Real × Real) => volume (⋃ i in Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2))
    totalLengthFilter (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun E => ENNReal.ofReal (∑ i in Finset.range E.1, (dist (E.2 i).1 (E.2 i).2)))
  · convert! ENNReal.tendsto_ofReal (Filter.tendsto_comap)
    simp
  · intro; simp
  · intro E
    simp only
    grw [measure_biUnion_finset_le]
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => dist_nonneg)]
    apply Eq.le
    apply Finset.sum_congr rfl
    simp [uIoc, Real.dist_eq, max_sub_min_eq_abs']

/--
lemma `tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero` / 引理 `tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero`

English:
lemma tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero
  given: (a b : Real)
  proof: by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun E : Nat × (Nat -> Real × Real) => volume (⋃ i in Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2))
  · apply tendsto_volume_totalLengthFilter_nhds_zero.mono_left
    simp
  · intro; simp
  · intro E
    simp only [Finse

中文:
引理 tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero
  条件: (a b : 实数)
  证明: by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun E : Nat × (Nat -> Real × Real) => volume (⋃ i in Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2))
  · apply tendsto_volume_totalLengthFilter_nhds_zero.mono_left
    simp
  · intro; simp
  · intro E
    simp only [Finse

Depends on / 依赖: Finset, Finset.mem_range, Finset.range, Measure, Measure.restrict_le_self, mem_range, mono_left, restrict_le_self, tendsto_const_nhds, tendsto_of_tendsto_of_tendsto_of_le_of_le, tendsto_volume_totalLengthFilter_nhds_zero, tendsto_volume_totalLengthFilter_nhds_zero.mono_left, volume
-/
lemma tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero (a b : Real) :
    Tendsto (fun E : Nat × (Nat -> Real × Real) => volume.restrict (uIoc a b)
        (⋃ i in Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b))
      (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h := fun E : Nat × (Nat -> Real × Real) => volume (⋃ i in Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2))
  · apply tendsto_volume_totalLengthFilter_nhds_zero.mono_left
    simp
  · intro; simp
  · intro E
    simp only [Finset.mem_range]
    apply Measure.restrict_le_self

/--
Definition of `_root_.AbsolutelyContinuousOnInterval` / `_root_.AbsolutelyContinuousOnInterval` 的定义

English:
definition _root_.AbsolutelyContinuousOnInterval
  signature: (f : Real -> X) (a b : Real)
  body: Tendsto (fun E => ∑ i in Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2))
    (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0)

中文:
定义 _root_.AbsolutelyContinuousOnInterval
  签名: (f : 实数 -> X) (a b : 实数)
  定义体: Tendsto (fun E => ∑ i in Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2))
    (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0)

Depends on / 依赖: Finset, Finset.range, Tendsto, disjWithin, totalLengthFilter
-/
def _root_.AbsolutelyContinuousOnInterval (f : Real -> X) (a b : Real) :=
  Tendsto (fun E => ∑ i in Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2))
    (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0)

/--
theorem `_root_.absolutelyContinuousOnInterval_iff` / 定理 `_root_.absolutelyContinuousOnInterval_iff`

English:
theorem _root_.absolutelyContinuousOnInterval_iff
  given: (f : Real -> X) (a b : Real)
  proof: by
  simp [AbsolutelyContinuousOnInterval, Metric.tendsto_nhds,
    Filter.HasBasis.eventually_iff (hasBasis_totalLengthFilter.inf_principal _),
    imp.swap, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => dist_nonneg))]

中文:
定理 _root_.absolutelyContinuousOnInterval_iff
  条件: (f : 实数 -> X) (a b : 实数)
  证明: by
  simp [AbsolutelyContinuousOnInterval, Metric.tendsto_nhds,
    Filter.HasBasis.eventually_iff (hasBasis_totalLengthFilter.inf_principal _),
    imp.swap, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => dist_nonneg))]

Depends on / 依赖: AbsolutelyContinuousOnInterval, Filter, Filter.HasBasis.eventually_iff, Finset, Finset.sum_nonneg, HasBasis, Metric, Metric.tendsto_nhds, abs_of_nonneg, dist_nonneg, eventually_iff, hasBasis_totalLengthFilter, hasBasis_totalLengthFilter.inf_principal, imp.swap, inf_principal, sum_nonneg, tendsto_nhds
-/
theorem _root_.absolutelyContinuousOnInterval_iff (f : Real -> X) (a b : Real) :
    AbsolutelyContinuousOnInterval f a b ↔
    forall ε > (0 : Real), exists δ > (0 : Real), forall E, E in disjWithin a b ->
    ∑ i in Finset.range E.1, dist (E.2 i).1 (E.2 i).2 < δ ->
    ∑ i in Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) < ε := by
  simp [AbsolutelyContinuousOnInterval, Metric.tendsto_nhds,
    Filter.HasBasis.eventually_iff (hasBasis_totalLengthFilter.inf_principal _),
    imp.swap, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => dist_nonneg))]

variable {f g : Real -> X} {a b c d : Real}

/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (hf : AbsolutelyContinuousOnInterval f a b)
  proof: by
  simp_all [AbsolutelyContinuousOnInterval, disjWithin_comm]

中文:
定理 symm
  条件: (hf : AbsolutelyContinuousOn整数erval f a b)
  证明: by
  simp_all [AbsolutelyContinuousOnInterval, disjWithin_comm]

Depends on / 依赖: AbsolutelyContinuousOnInterval, disjWithin_comm
-/
theorem symm (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval f b a := by
  simp_all [AbsolutelyContinuousOnInterval, disjWithin_comm]

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (hf : AbsolutelyContinuousOnInterval f a b) (habcd : uIcc c d subseteq uIcc a b)
  proof: by
  simp only [AbsolutelyContinuousOnInterval, Tendsto] at *
  refine le_trans (Filter.map_mono ?_) hf
  gcongr; exact disjWithin_mono habcd

中文:
定理 mono
  条件: (hf : AbsolutelyContinuousOn整数erval f a b) (habcd : uIcc c d subseteq uIcc a b)
  证明: by
  simp only [AbsolutelyContinuousOnInterval, Tendsto] at *
  refine le_trans (Filter.map_mono ?_) hf
  gcongr; exact disjWithin_mono habcd

Depends on / 依赖: AbsolutelyContinuousOnInterval, Filter, Filter.map_mono, Tendsto, disjWithin_mono, le_trans, map_mono
-/
theorem mono (hf : AbsolutelyContinuousOnInterval f a b) (habcd : uIcc c d subseteq uIcc a b) :
    AbsolutelyContinuousOnInterval f c d := by
  simp only [AbsolutelyContinuousOnInterval, Tendsto] at *
  refine le_trans (Filter.map_mono ?_) hf
  gcongr; exact disjWithin_mono habcd

variable {f g : Real -> F}

@[to_fun]
/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: (hf : AbsolutelyContinuousOnInterval f a b)
  proof: by
  apply squeeze_zero (fun t => ?_) (fun t => ?_) (by simpa using Tendsto.add hf hg)
  · exact Finset.sum_nonneg (fun i hi => by positivity)
  · rw [← Finset.sum_add_distrib]
    gcongr
    exact dist_add_add_le _ _ _ _

@[to_fun]

中文:
定理 add
  结论: (hf : AbsolutelyContinuousOn整数erval f a b)
  证明: by
  apply squeeze_zero (fun t => ?_) (fun t => ?_) (by simpa using Tendsto.add hf hg)
  · exact Finset.sum_nonneg (fun i hi => by positivity)
  · rw [← Finset.sum_add_distrib]
    gcongr
    exact dist_add_add_le _ _ _ _

@[to_fun]

Depends on / 依赖: Finset, Finset.sum_add_distrib, Finset.sum_nonneg, Tendsto, Tendsto.add, dist_add_add_le, squeeze_zero, sum_add_distrib, sum_nonneg
-/
theorem add (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f + g) a b := by
  apply squeeze_zero (fun t => ?_) (fun t => ?_) (by simpa using Tendsto.add hf hg)
  · exact Finset.sum_nonneg (fun i hi => by positivity)
  · rw [← Finset.sum_add_distrib]
    gcongr
    exact dist_add_add_le _ _ _ _

@[to_fun]
/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (hf : AbsolutelyContinuousOnInterval f a b)
  proof: by
  apply squeeze_zero (fun t => ?_) (fun t => ?_) (by simpa using! hf)
  · exact Finset.sum_nonneg (fun i hi => by positivity)
  · simp

@[to_fun]

中文:
定理 neg
  条件: (hf : AbsolutelyContinuousOn整数erval f a b)
  证明: by
  apply squeeze_zero (fun t => ?_) (fun t => ?_) (by simpa using! hf)
  · exact Finset.sum_nonneg (fun i hi => by positivity)
  · simp

@[to_fun]

Depends on / 依赖: Finset, Finset.sum_nonneg, squeeze_zero, sum_nonneg
-/
theorem neg (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (-f) a b := by
  apply squeeze_zero (fun t => ?_) (fun t => ?_) (by simpa using! hf)
  · exact Finset.sum_nonneg (fun i hi => by positivity)
  · simp

@[to_fun]
/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  statement: (hf : AbsolutelyContinuousOnInterval f a b)
  proof: by
  simpa [sub_eq_add_neg] using hf.add (hg.neg)

中文:
定理 sub
  结论: (hf : AbsolutelyContinuousOn整数erval f a b)
  证明: by
  simpa [sub_eq_add_neg] using hf.add (hg.neg)

Depends on / 依赖: hf.add, hg.neg, sub_eq_add_neg
-/
theorem sub (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f - g) a b := by
  simpa [sub_eq_add_neg] using hf.add (hg.neg)

/--
theorem `const_smul` / 定理 `const_smul`

English:
theorem const_smul
  statement: {M : Type*} [SeminormedRing M] [Module M F] [NormSMulClass M F]
  proof: by
  apply squeeze_zero (fun t => ?_) (fun t => ?_) (by simpa using hf.const_mul ‖α‖)
  · exact Finset.sum_nonneg (fun i hi => by positivity)
  · simp [Finset.mul_sum, dist_smul₀]

中文:
定理 const_smul
  结论: {M : 类型} [SeminormedRing M] [Module M F] [NormSMulClass M F]
  证明: by
  apply squeeze_zero (fun t => ?_) (fun t => ?_) (by simpa using hf.const_mul ‖α‖)
  · exact Finset.sum_nonneg (fun i hi => by positivity)
  · simp [Finset.mul_sum, dist_smul₀]

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_nonneg, const_mul, hf.const_mul, mul_sum, squeeze_zero, sum_nonneg
-/
theorem const_smul {M : Type*} [SeminormedRing M] [Module M F] [NormSMulClass M F]
    (α : M) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => α • f x) a b := by
  apply squeeze_zero (fun t => ?_) (fun t => ?_) (by simpa using hf.const_mul ‖α‖)
  · exact Finset.sum_nonneg (fun i hi => by positivity)
  · simp [Finset.mul_sum, dist_smul₀]

/--
theorem `const_mul` / 定理 `const_mul`

English:
theorem const_mul
  given: {f : Real -> Real} (α : Real) (hf : AbsolutelyContinuousOnInterval f a b)
  proof: hf.const_smul α

中文:
定理 const_mul
  条件: {f : 实数 -> 实数} (α : 实数) (hf : AbsolutelyContinuousOn整数erval f a b)
  证明: hf.const_smul α

Depends on / 依赖: const_smul, hf.const_smul
-/
theorem const_mul {f : Real -> Real} (α : Real) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => α * f x) a b :=
  hf.const_smul α

/--
lemma `uniformity_eq_comap_totalLengthFilter` / 引理 `uniformity_eq_comap_totalLengthFilter`

English:
lemma uniformity_eq_comap_totalLengthFilter
  proof: by
  refine Filter.HasBasis.eq_of_same_basis Metric.uniformity_basis_dist ?_
  convert! hasBasis_totalLengthFilter.comap _
  simp

中文:
引理 uniformity_eq_comap_totalLengthFilter
  证明: by
  refine Filter.HasBasis.eq_of_same_basis Metric.uniformity_basis_dist ?_
  convert! hasBasis_totalLengthFilter.comap _
  simp

Depends on / 依赖: Filter, Filter.HasBasis.eq_of_same_basis, HasBasis, Metric, Metric.uniformity_basis_dist, convert, eq_of_same_basis, hasBasis_totalLengthFilter, hasBasis_totalLengthFilter.comap, uniformity_basis_dist
-/
lemma uniformity_eq_comap_totalLengthFilter :
    uniformity X = comap (fun x => (1, fun _ => x)) totalLengthFilter := by
  refine Filter.HasBasis.eq_of_same_basis Metric.uniformity_basis_dist ?_
  convert! hasBasis_totalLengthFilter.comap _
  simp

/--
theorem `uniformContinuousOn` / 定理 `uniformContinuousOn`

English:
theorem uniformContinuousOn
  given: (hf : AbsolutelyContinuousOnInterval f a b)
  proof: by
  simp only [UniformContinuousOn, Filter.tendsto_iff_comap, uniformity_eq_comap_totalLengthFilter]
  simp only [AbsolutelyContinuousOnInterval, Filter.tendsto_iff_comap] at hf
  convert! Filter.comap_mono hf
  · simp only [comap_inf, comap_principal]
    congr
    ext p
    simp only [disjWithin,

中文:
定理 uniformContinuousOn
  条件: (hf : AbsolutelyContinuousOn整数erval f a b)
  证明: by
  simp only [UniformContinuousOn, Filter.tendsto_iff_comap, uniformity_eq_comap_totalLengthFilter]
  simp only [AbsolutelyContinuousOnInterval, Filter.tendsto_iff_comap] at hf
  convert! Filter.comap_mono hf
  · simp only [comap_inf, comap_principal]
    congr
    ext p
    simp only [disjWithin,

Depends on / 依赖: AbsolutelyContinuousOnInterval, Filter, Filter.comap_mono, Filter.tendsto_iff_comap, Finset, Finset.mem_range, Function, Function.comp_def, Nat.lt_one_iff, UniformContinuousOn, comap_comap, comap_inf, comap_mono, comap_principal, comp_def, convert, disjWithin, forall_eq, lt_one_iff, mem_ofPred_eq
-/
theorem uniformContinuousOn (hf : AbsolutelyContinuousOnInterval f a b) :
    UniformContinuousOn f (uIcc a b) := by
  simp only [UniformContinuousOn, Filter.tendsto_iff_comap, uniformity_eq_comap_totalLengthFilter]
  simp only [AbsolutelyContinuousOnInterval, Filter.tendsto_iff_comap] at hf
  convert! Filter.comap_mono hf
  · simp only [comap_inf, comap_principal]
    congr
    ext p
    simp only [disjWithin, Finset.mem_range, preimage_ofPred_eq, Nat.lt_one_iff,
      forall_eq, mem_ofPred_eq, mem_prod]
    simp
  · simp [totalLengthFilter, comap_comap, Function.comp_def]

@[deprecated (since := "2026-02-03")] alias uniformlyContinuousOn :=
  uniformContinuousOn

/--
theorem `continuousOn` / 定理 `continuousOn`

English:
theorem continuousOn
  given: (hf : AbsolutelyContinuousOnInterval f a b)
  proof: hf.uniformContinuousOn.continuousOn

中文:
定理 continuousOn
  条件: (hf : AbsolutelyContinuousOn整数erval f a b)
  证明: hf.uniformContinuousOn.continuousOn

Depends on / 依赖: continuousOn, hf.uniformContinuousOn.continuousOn, uniformContinuousOn
-/
theorem continuousOn (hf : AbsolutelyContinuousOnInterval f a b) :
    ContinuousOn f (uIcc a b) :=
  hf.uniformContinuousOn.continuousOn

/--
theorem `exists_bound` / 定理 `exists_bound`

English:
theorem exists_bound
  given: (hf : AbsolutelyContinuousOnInterval f a b)
  proof: isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn)

中文:
定理 exists_bound
  条件: (hf : AbsolutelyContinuousOn整数erval f a b)
  证明: isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn)

Depends on / 依赖: continuousOn, exists_bound_of_continuousOn, hf.continuousOn, isCompact_Icc, isCompact_Icc.exists_bound_of_continuousOn
-/
theorem exists_bound (hf : AbsolutelyContinuousOnInterval f a b) :
    exists (C : Real), forall x in uIcc a b, ‖f x‖ <= C :=
  isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn)

/-- If `f` and `g` are absolutely continuous on `uIcc a b`, then `f • g` is absolutely continuous
on `uIcc a b`. -/
@[to_fun]
/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: {M : Type*} [SeminormedRing M] [Module M F] [NormSMulClass M F]
  proof: by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨D, hD⟩ := hg.exists_bound
  unfold AbsolutelyContinuousOnInterval at hf hg
  apply squeeze_zero' ?_ ?_
    (by simpa using (hg.const_mul C).add (hf.const_mul D))
· exact Filter.Eventually.of_forall fun _ => Finset.sum_nonneg (fun i hi => dist_nonneg)


中文:
定理 smul
  结论: {M : 类型} [SeminormedRing M] [Module M F] [NormSMulClass M F]
  证明: by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨D, hD⟩ := hg.exists_bound
  unfold AbsolutelyContinuousOnInterval at hf hg
  apply squeeze_zero' ?_ ?_
    (by simpa using (hg.const_mul C).add (hf.const_mul D))
· exact Filter.Eventually.of_forall fun _ => Finset.sum_nonneg (fun i hi => dist_nonneg)


Depends on / 依赖: AbsolutelyContinuousOnInterval, Eventually, Filter, Filter.Eventually.of_forall, Finset, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_nonneg, const_mul, dist_nonneg, eventually_inf_principal, exists_bound, filter_upwards, hf.const_mul, hf.exists_bound, hg.const_mul, hg.exists_bound, mul_sum, of_forall, squeeze_zero
-/
theorem smul {M : Type*} [SeminormedRing M] [Module M F] [NormSMulClass M F]
    {f : Real -> M} {g : Real -> F}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f • g) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨D, hD⟩ := hg.exists_bound
  unfold AbsolutelyContinuousOnInterval at hf hg
  apply squeeze_zero' ?_ ?_
    (by simpa using (hg.const_mul C).add (hf.const_mul D))
· exact Filter.Eventually.of_forall fun _ => Finset.sum_nonneg (fun i hi => dist_nonneg)
  rw [eventually_inf_principal]
  filter_upwards with (n, I) hnI
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  gcongr with i hi
  trans dist (f (I i).1 • g (I i).1) (f (I i).1 • g (I i).2) +
    dist (f (I i).1 • g (I i).2) (f (I i).2 • g (I i).2)
  · exact dist_triangle _ _ _
  · simp only [disjWithin, mem_ofPred_eq] at hnI
    gcongr
    · rw [dist_smul₀]
      gcongr
      exact hC _ (hnI.left i hi |>.left)
    · rw [mul_comm]
      grw [dist_pair_smul]
      gcongr
      rw [dist_zero_right]
      exact hD _ (hnI.left i hi |>.right)

/-- If `f` and `g` are absolutely continuous on `uIcc a b`, then `f * g` is absolutely continuous
on `uIcc a b`. -/
@[to_fun]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: {f g : Real -> Real}
  proof: hf.smul hg

中文:
定理 mul
  结论: {f g : 实数 -> 实数}
  证明: hf.smul hg

Depends on / 依赖: hf.smul
-/
theorem mul {f g : Real -> Real}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f * g) a b :=
  hf.smul hg

/--
theorem `_root_.LipschitzOnWith.absolutelyContinuousOnInterval` / 定理 `_root_.LipschitzOnWith.absolutelyContinuousOnInterval`

English:
theorem _root_.LipschitzOnWith.absolutelyContinuousOnInterval
  statement: {f : Real -> X} {K : Real>=0}
  proof: by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  refine ⟨ε / (K + 1), by positivity, fun (n, I) hnI₁ hnI₂ => ?_⟩
  calc
    _ <= ∑ i in Finset.range n, K * dist (I i).1 (I i).2 := by
      apply Finset.sum_le_sum
      intro i hi
      have := hfK (hnI₁.left i hi).left (hnI₁.left i hi).ri

中文:
定理 _root_.LipschitzOnWith.absolutelyContinuousOnInterval
  结论: {f : 实数 -> X} {K : 实数>=0}
  证明: by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  refine ⟨ε / (K + 1), by positivity, fun (n, I) hnI₁ hnI₂ => ?_⟩
  calc
    _ <= ∑ i in Finset.range n, K * dist (I i).1 (I i).2 := by
      apply Finset.sum_le_sum
      intro i hi
      have := hfK (hnI₁.left i hi).left (hnI₁.left i hi).ri

Depends on / 依赖: ENNReal, ENNReal.toReal_mono, ENNReal.toReal_mul, Finset, Finset.mul_sum, Finset.range, Finset.sum_le_sum, Ne.symm, absolutelyContinuousOnInterval_iff, dist_edist, mul_sum, not_eq_of_beq_eq_false, sum_le_sum, toReal_mono, toReal_mul
-/
theorem _root_.LipschitzOnWith.absolutelyContinuousOnInterval {f : Real -> X} {K : Real>=0}
    (hfK : LipschitzOnWith K f (uIcc a b)) : AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  refine ⟨ε / (K + 1), by positivity, fun (n, I) hnI₁ hnI₂ => ?_⟩
  calc
    _ <= ∑ i in Finset.range n, K * dist (I i).1 (I i).2 := by
      apply Finset.sum_le_sum
      intro i hi
      have := hfK (hnI₁.left i hi).left (hnI₁.left i hi).right
      apply ENNReal.toReal_mono (Ne.symm (not_eq_of_beq_eq_false rfl)) at this
      rwa [ENNReal.toReal_mul, ← dist_edist, ← dist_edist] at this
    _ = K * ∑ i in Finset.range n, dist (I i).1 (I i).2 := by symm; exact Finset.mul_sum _ _ _
    _ <= K * (ε / (K + 1)) := by gcongr
    _ < (K + 1) * (ε / (K + 1)) := by gcongr; linarith
    _ = ε := by field

/--
theorem `_root_.ContDiffOn.absolutelyContinuousOnInterval` / 定理 `_root_.ContDiffOn.absolutelyContinuousOnInterval`

English:
theorem _root_.ContDiffOn.absolutelyContinuousOnInterval
  statement: {E : Type*} [NormedAddCommGroup E]
  proof: by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  exact hK.absolutelyContinuousOnInterval

中文:
定理 _root_.ContDiffOn.absolutelyContinuousOnInterval
  结论: {E : 类型} [NormedAddCommGroup E]
  证明: by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  exact hK.absolutelyContinuousOnInterval

Depends on / 依赖: absolutelyContinuousOnInterval, convex_Icc, exists_lipschitzOnWith, hK.absolutelyContinuousOnInterval, hf.exists_lipschitzOnWith, isCompact_Icc
-/
theorem _root_.ContDiffOn.absolutelyContinuousOnInterval {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] {f : Real -> E} (hf : ContDiffOn Real 1 f (uIcc a b)) :
    AbsolutelyContinuousOnInterval f a b := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  exact hK.absolutelyContinuousOnInterval

/--
theorem `boundedVariationOn` / 定理 `boundedVariationOn`

English:
theorem boundedVariationOn
  given: (hf : AbsolutelyContinuousOnInterval f a b)
  proof: by
  -- We may assume wlog that `a ≤ b`.
  wlog hab₀ : a <= b generalizing a b
  · specialize @this b a hf.symm (by linarith)
    rwa [uIcc_comm]
  rw [uIcc_of_le hab₀]
  -- Split the cases `a = b` (which is trivial) and `a < b`.
  rcases hab₀.eq_or_lt with rfl | hab
  · simp [BoundedVariationOn]
  

中文:
定理 boundedVariationOn
  条件: (hf : AbsolutelyContinuousOn整数erval f a b)
  证明: by
  -- We may assume wlog that `a ≤ b`.
  wlog hab₀ : a <= b generalizing a b
  · specialize @this b a hf.symm (by linarith)
    rwa [uIcc_comm]
  rw [uIcc_of_le hab₀]
  -- Split the cases `a = b` (which is trivial) and `a < b`.
  rcases hab₀.eq_or_lt with rfl | hab
  · simp [BoundedVariationOn]
  
-/
theorem boundedVariationOn (hf : AbsolutelyContinuousOnInterval f a b) :
    BoundedVariationOn f (uIcc a b) := by
  -- We may assume wlog that `a ≤ b`.
  wlog hab₀ : a <= b generalizing a b
  · specialize @this b a hf.symm (by linarith)
    rwa [uIcc_comm]
  rw [uIcc_of_le hab₀]
  -- Split the cases `a = b` (which is trivial) and `a < b`.
  rcases hab₀.eq_or_lt with rfl | hab
  · simp [BoundedVariationOn]
  -- Now remains the case `a < b`.
  -- Use the `ε`-`δ` definition of AC to get a `δ > 0` such that whenever a finite set of disjoint
  -- intervals `uIoc (a i) (b i)`, `i < n` have total length `< δ` and `a i, b i` are all in
  -- `[a, b]`, we have `∑ i ∈ range n, dist (f (a i)) (f (b i)) < 1`.
  rw [absolutelyContinuousOnInterval_iff] at hf
  obtain ⟨δ, hδ₁, hδ₂⟩ := hf 1 (by linarith)
  have hab₁ : 0 < b - a := by linarith
  -- Split `[a, b]` into subintervals `[a + i * δ', a + (i + 1) * δ']` for `i = 0, ..., n`, where
  -- `a + (n + 1) * δ' = b` and `δ' < δ`.
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hδ₁ hab₁)
  set δ' := (b - a) / (n + 1)
  have hδ₃ : δ' < δ := by
    dsimp only [δ']
    convert! mul_lt_mul_of_pos_right hn hab₁ using 1 <;> field
  have h_mono : Monotone fun (i : Nat) => a + ↑i * δ' := by
    apply Monotone.const_add
    apply Monotone.mul_const Nat.mono_cast
    simp only [δ']
    refine div_nonneg ?_ ?_ <;> linarith
  -- The variation of `f` on `[a, b]` is the sum of the variations on these subintervals.
  have v_sum : eVariationOn f (Icc a b) =
      ∑ i in Finset.range (n + 1), eVariationOn f (Icc (a + i * δ') (a + (i + 1) * δ')) := by
.symm convert! eVariationOn.sum' f (I := fun i => a + i * δ') h_mono
    · simp
    · simp only [Nat.cast_add, Nat.cast_one, δ']; field
    · norm_cast
  -- The variation of `f` on any subinterval `[x, y]` of `[a, b]` of length `< δ` is `≤ 1`.
  have v_each (x y : Real) (_ : a <= x) (_ : x <= y) (_ : y < x + δ) (_ : y <= b) :
      eVariationOn f (Icc x y) <= 1 := by
    simp only [eVariationOn, iSup_le_iff]
    intro p
    obtain ⟨hp₁, hp₂⟩ := p.2.property
    -- Focus on a partition `p` of `[x, y]` and show its variation with `f` is `≤ 1`.
    have vf : ∑ i in Finset.range p.1, dist (f (p.2.val i)) (f (p.2.val (i + 1))) < 1 := by
      apply hδ₂ (p.1, (fun i => (p.2.val i, p.2.val (i + 1))))
      · constructor
        · have : Icc x y subseteq uIcc a b := by rw [uIcc_of_le hab₀]; gcongr
          intro i hi
          constructor <;> exact this (hp₂ _)
        · rw [PairwiseDisjoint]
          convert! hp₁.pairwise_disjoint_on_Ioc_succ.set_pairwise (Finset.range p.1) using 3
          rw [uIoc_of_le (hp₁ (by lia))]; rw [Nat.succ_eq_succ]
      · suffices p.2.val p.1 - p.2.val 0 < δ by
          convert! this
          rw [← Finset.sum_range_sub]
          congr; ext i
          rw [dist_comm]; rw [Real.dist_eq]; rw [abs_eq_self.mpr]
          linarith [@hp₁ i (i + 1) (by lia)]
        linarith [mem_Icc.mp (hp₂ p.1), mem_Icc.mp (hp₂ 0)]
    -- Reduce edist in the goal to dist and clear up
    have veq : (∑ i in Finset.range p.1, edist (f (p.2.val (i + 1))) (f (p.2.val i))).toReal =
        ∑ i in Finset.range p.1, dist (f (p.2.val i)) (f (p.2.val (i + 1))) := by
      rw [ENNReal.toReal_sum (by simp [edist_ne_top])]
      simp_rw [← dist_edist]; congr; ext i; nth_rw 1 [dist_comm]
    have not_top : ∑ i in Finset.range p.1, edist (f (p.2.val (i + 1))) (f (p.2.val i)) != ⊤ := by
      simp [edist_ne_top]
    rw [← ENNReal.ofReal_toReal not_top]
    convert! ENNReal.ofReal_le_ofReal (veq.symm ▸ vf.le)
    simp
  -- Reduce to goal that the variation of `f` on each of these subintervals is finite.
  simp only [BoundedVariationOn, v_sum, ne_eq, ENNReal.sum_eq_top, Finset.mem_range, not_exists,
    not_and]
  intro i hi
  -- Reduce finiteness to `≤ 1`.
  suffices eVariationOn f (Icc (a + i * δ') (a + (i + 1) * δ')) <= 1 from
    fun hC => by simp [hC] at this
  -- Verify that `[a + i * δ', a + (i + 1) * δ']` is indeed a subinterval of `[a, b]`
  apply v_each
  · convert! h_mono (show 0 <= i by lia); simp
  · convert! h_mono (show i <= i + 1 by lia); norm_cast
  · rw [add_mul, ← add_assoc]; simpa
  · convert! h_mono (show i + 1 <= n + 1 by lia)
    · norm_cast
    · simp only [Nat.cast_add, Nat.cast_one, δ']; field

/--
theorem `ae_differentiableAt` / 定理 `ae_differentiableAt`

English:
theorem ae_differentiableAt
  statement: {f : Real -> Real} {a b : Real}
  proof: hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc

中文:
定理 ae_differentiableAt
  结论: {f : 实数 -> 实数} {a b : 实数}
  证明: hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc

Depends on / 依赖: ae_differentiableAt_of_mem_uIcc, boundedVariationOn, hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
-/
theorem ae_differentiableAt {f : Real -> Real} {a b : Real}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    forallᵐ (x : Real), x in uIcc a b -> DifferentiableAt Real f x :=
  hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc

/--
theorem `_root_.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral` / 定理 `_root_.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`

English:
theorem _root_.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
  statement: {f : Real -> Real}
  proof: by
  -- Step 1: Use `MeasureTheory.tendsto_setLIntegral_zero` to conclude that the function sending
  -- `E` to `∫⁻ (x : ℝ) in s E, ‖f x‖ₑ ∂volume.restrict (uIoc a b))` tends to `0` along
  -- `totalLengthFilter ⊓ 𝓟 (disjWithin a b)`.
  let s := fun E : Nat × (Nat -> Real × Real) => ⋃ i in Finset.ra

中文:
定理 _root_.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
  结论: {f : 实数 -> 实数}
  证明: by
  -- Step 1: Use `MeasureTheory.tendsto_setLIntegral_zero` to conclude that the function sending
  -- `E` to `∫⁻ (x : ℝ) in s E, ‖f x‖ₑ ∂volume.restrict (uIoc a b))` tends to `0` along
  -- `totalLengthFilter ⊓ 𝓟 (disjWithin a b)`.
  let s := fun E : Nat × (Nat -> Real × Real) => ⋃ i in Finset.ra
-/
theorem _root_.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral {f : Real -> Real}
    {a b c : Real} (h : IntervalIntegrable f volume a b) (hc : c in uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ v in c..x, f v) a b := by
  -- Step 1: Use `MeasureTheory.tendsto_setLIntegral_zero` to conclude that the function sending
  -- `E` to `∫⁻ (x : ℝ) in s E, ‖f x‖ₑ ∂volume.restrict (uIoc a b))` tends to `0` along
  -- `totalLengthFilter ⊓ 𝓟 (disjWithin a b)`.
  let s := fun E : Nat × (Nat -> Real × Real) => ⋃ i in Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have : Tendsto (fun i => ∫⁻ (x : Real) in s i, ‖f x‖ₑ ∂volume.restrict (uIoc a b))
      (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero
    (ne_of_lt <| intervalIntegrable_iff.mp h |>.hasFiniteIntegral)
    (tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero _ _)
  -- Step 2: Use the lintegral in Step 1 to bound the sum of the distances between
  -- `∫ v in c..(E.2 i).2, f v` and `∫ v in c..(E.2 i).2, f v` that occurs in the definition
  -- of absolutely continuous.
  have := ENNReal.toReal_zero ▸ (ENNReal.continuousAt_toReal (by simp)).tendsto.comp this
  refine squeeze_zero' ?_ ?_ this
  · filter_upwards with (n, I)
    exact Finset.sum_nonneg (fun _ _ => dist_nonneg)
  simp only [comp_apply, s]
  have : forallᶠ (E : Nat × (Nat -> Real × Real)) in totalLengthFilter ⊓ 𝓟 (disjWithin a b),
      E in disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [this] with (n, I) hnI
  obtain ⟨hnI1, hnI2⟩ := mem_ofPred_eq ▸ hnI
  simp only
  rw [← integral_norm_eq_lintegral_enorm (h.aestronglyMeasurable_restrict_uIoc.restrict)]; rw [integral_biUnion_finset _ (by simp +contextual [uIoc]) hnI2]
  · refine Finset.sum_le_sum (fun i hi => ?_)
    rw [Real.dist_eq]; rw [intervalIntegral.integral_interval_sub_left
          (by apply IntervalIntegrable.mono_set' h; grind [uIoc]; rw [uIcc])
          (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc]),
        Measure.restrict_restrict_of_subset
          (uIoc_subset_of_mem_disjWithin hnI (Finset.mem_range.mp hi)),
        intervalIntegral.integral_symm, abs_neg,
        intervalIntegral.abs_intervalIntegral_eq]
    exact abs_integral_le_integral_abs
  · intro i hi
    unfold IntegrableOn
    have h_subset := uIoc_subset_of_mem_disjWithin hnI (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset h_subset]
.integrable exact IntegrableOn.mono_set h.def'.norm h_subset

end AbsolutelyContinuousOnInterval
