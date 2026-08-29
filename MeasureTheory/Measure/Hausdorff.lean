/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.MetricSpace.MetricSeparated
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Hausdorff measure and metric (outer) measures

In this file we define the `d`-dimensional Hausdorff measure on an (extended) metric space `X` and
the Hausdorff dimension of a set in an (extended) metric space. Let `μ d δ` be the maximal outer
measure such that `μ d δ s ≤ (ediam s) ^ d` for every set of diameter less than `δ`. Then
the Hausdorff measure `μH[d] s` of `s` is defined as `⨆ δ > 0, μ d δ s`. By Carathéodory's theorem
`MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`, this is a Borel measure on `X`.

The value of `μH[d]`, `d > 0`, on a set `s` (measurable or not) is given by
```
μH[d] s = ⨆ (r : ℝ≥0∞) (hr : 0 < r), ⨅ (t : ℕ → Set X) (hts : s ⊆ ⋃ n, t n)
    (ht : ∀ n, ediam (t n) ≤ r), ∑' n, ediam (t n) ^ d
```

For every set `s` and any `d < d'` we have either `μH[d] s = ∞` or `μH[d'] s = 0`, see
`MeasureTheory.Measure.hausdorffMeasure_zero_or_top`. In
`Mathlib/Topology/MetricSpace/HausdorffDimension.lean` we use this fact to define the Hausdorff
dimension `dimH` of a set in an (extended) metric space.

We also define two generalizations of the Hausdorff measure. In one generalization (see
`MeasureTheory.Measure.mkMetric`) we take any function `m (diam s)` instead of `(diam s) ^ d`. In
an even more general definition (see `MeasureTheory.Measure.mkMetric'`) we use any function
of `m : Set X → ℝ≥0∞`. Some authors start with a partial function `m` defined only on some sets
`s : Set X` (e.g., only on balls or only on measurable sets). This is equivalent to our definition
applied to `MeasureTheory.extend m`.

We also define a predicate `MeasureTheory.OuterMeasure.IsMetric` which says that an outer measure
is additive on metric separated pairs of sets: `μ (s ∪ t) = μ s + μ t` provided that
`⨅ (x ∈ s) (y ∈ t), edist x y ≠ 0`. This is the property required for Carathéodory's theorem
`MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`, so we prove this theorem for any
metric outer measure, then prove that outer measures constructed using `mkMetric'` are metric outer
measures.

## Main definitions

* `MeasureTheory.OuterMeasure.IsMetric`: an outer measure `μ` is called *metric* if
  `μ (s ∪ t) = μ s + μ t` for any two metric separated sets `s` and `t`. A metric outer measure in a
  Borel extended metric space is guaranteed to satisfy the Carathéodory condition, see
  `MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`.
* `MeasureTheory.OuterMeasure.mkMetric'` and its particular case
  `MeasureTheory.OuterMeasure.mkMetric`: a construction of an outer measure that is guaranteed to
  be metric. Both constructions are generalizations of the Hausdorff measure. The same measures
  interpreted as Borel measures are called `MeasureTheory.Measure.mkMetric'` and
  `MeasureTheory.Measure.mkMetric`.
* `MeasureTheory.Measure.hausdorffMeasure` a.k.a. `μH[d]`: the `d`-dimensional Hausdorff measure.
  There are many definitions of the Hausdorff measure that differ from each other by a
  multiplicative constant. We put
  `μH[d] s = ⨆ r > 0, ⨅ (t : ℕ → Set X) (hts : s ⊆ ⋃ n, t n) (ht : ∀ n, ediam (t n) ≤ r),
    ∑' n, ⨆ (ht : ¬Set.Subsingleton (t n)), (ediam (t n)) ^ d`,
  see `MeasureTheory.Measure.hausdorffMeasure_apply`. In the most interesting case `0 < d` one
  can omit the `⨆ (ht : ¬Set.Subsingleton (t n))` part.

## Main statements

### Basic properties

* `MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`: if `μ` is a metric outer measure
  on an extended metric space `X` (that is, it is additive on pairs of metric separated sets), then
  every Borel set is Carathéodory measurable (hence, `μ` defines an actual
  `MeasureTheory.Measure`). See also `MeasureTheory.Measure.mkMetric`.
* `MeasureTheory.Measure.hausdorffMeasure_mono`: `μH[d] s` is an antitone function
  of `d`.
* `MeasureTheory.Measure.hausdorffMeasure_zero_or_top`: if `d₁ < d₂`, then for any `s`, either
  `μH[d₂] s = 0` or `μH[d₁] s = ∞`. Together with the previous lemma, this means that `μH[d] s` is
  equal to infinity on some ray `(-∞, D)` and is equal to zero on `(D, +∞)`, where `D` is a possibly
  infinite number called the *Hausdorff dimension* of `s`; `μH[D] s` can be zero, infinity, or
  anything in between.
* `MeasureTheory.Measure.nullSingletonClass_hausdorff`: Hausdorff measure has value zero on
  singletons.

### Hausdorff measure in `ℝⁿ`

* `MeasureTheory.hausdorffMeasure_pi_real`: for a nonempty `ι`, `μH[card ι]` on `ι → ℝ` equals
  Lebesgue measure.

## Notation

We use the following notation localized in `MeasureTheory`.

- `μH[d]` : `MeasureTheory.Measure.hausdorffMeasure d`

## Implementation notes

There are a few similar constructions called the `d`-dimensional Hausdorff measure. E.g., some
sources only allow coverings by balls and use `r ^ d` instead of `(diam s) ^ d`. While these
construction lead to different Hausdorff measures, they lead to the same notion of the Hausdorff
dimension.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.10][Federer1996]

## Tags

Hausdorff measure, measure, metric measure
-/

@[expose] public section


open scoped NNReal ENNReal Topology

open Metric EMetric Set Function Filter Encodable Module TopologicalSpace

noncomputable section

variable {ι X Y : Type*} [EMetricSpace X] [EMetricSpace Y]

namespace MeasureTheory

namespace OuterMeasure

/-!
### Metric outer measures

In this section we define metric outer measures and prove Carathéodory's theorem: a metric outer
measure has the Carathéodory property.
-/


/--
Definition of `IsMetric` / `IsMetric` 的定义

English:
definition IsMetric
  signature: (μ : OuterMeasure X)
  body: forall s t : Set X, Metric.AreSeparated s t -> μ (s union t) = μ s + μ t

中文:
定义 IsMetric
  签名: (μ : 外测度 X)
  定义体: forall s t : Set X, Metric.AreSeparated s t -> μ (s union t) = μ s + μ t

Depends on / 依赖: AreSeparated, Metric, Metric.AreSeparated
-/
def IsMetric (μ : OuterMeasure X) : Prop :=
  forall s t : Set X, Metric.AreSeparated s t -> μ (s union t) = μ s + μ t

namespace IsMetric

variable {μ : OuterMeasure X}

/--
theorem `finset_iUnion_of_pairwise_separated` / 定理 `finset_iUnion_of_pairwise_separated`

English:
theorem finset_iUnion_of_pairwise_separated
  statement: (hm : IsMetric μ) {I : Finset ι} {s : ι -> Set X}
  proof: by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hiI ihI =>
    simp only [Finset.mem_insert] at hI
    rw [Finset.set_biUnion_insert]; rw [hm]; rw [ihI]; rw [Finset.sum_insert hiI]
    exacts [fun i hi j hj hij => hI i (Or.inr hi) j (Or.inr hj) hij,
      Metric.AreSeparated.finset_iUnion_right fun j hj =>
        hI i (Or.inl rfl) j (Or.inr hj) (ne_of_mem_of_not_mem hj hiI).symm]

中文:
定理 finset_iUnion_of_pairwise_separated
  结论: (hm : IsMetric μ) {I : 有限集 ι} {s : ι -> 集合 X}
  证明: by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hiI ihI =>
    simp only [Finset.mem_insert] at hI
    rw [Finset.set_biUnion_insert]; rw [hm]; rw [ihI]; rw [Finset.sum_insert hiI]
    exacts [fun i hi j hj hij => hI i (Or.inr hi) j (Or.inr hj) hij,
      Metric.AreSeparated.finset_iUnion_right fun j hj =>
        hI i (Or.inl rfl) j (Or.inr hj) (ne_of_mem_of_not_mem hj hiI).symm]

Depends on / 依赖: AreSeparated, Finset, Finset.induction_on, Finset.mem_insert, Finset.set_biUnion_insert, Finset.sum_insert, Metric, Metric.AreSeparated.finset_iUnion_right, Or.inl, Or.inr, classical, exacts, finset_iUnion_right, induction_on, insert, mem_insert, ne_of_mem_of_not_mem, set_biUnion_insert, sum_insert
-/
theorem finset_iUnion_of_pairwise_separated (hm : IsMetric μ) {I : Finset ι} {s : ι -> Set X}
    (hI : forall i in I, forall j in I, i != j -> Metric.AreSeparated (s i) (s j)) :
    μ (⋃ i in I, s i) = ∑ i in I, μ (s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hiI ihI =>
    simp only [Finset.mem_insert] at hI
    rw [Finset.set_biUnion_insert]; rw [hm]; rw [ihI]; rw [Finset.sum_insert hiI]
    exacts [fun i hi j hj hij => hI i (Or.inr hi) j (Or.inr hj) hij,
      Metric.AreSeparated.finset_iUnion_right fun j hj =>
        hI i (Or.inl rfl) j (Or.inr hj) (ne_of_mem_of_not_mem hj hiI).symm]

/--
theorem `borel_le_caratheodory` / 定理 `borel_le_caratheodory`

English:
theorem borel_le_caratheodory
  given: (hm : IsMetric μ)
  statement: borel X <= μ.caratheodory
  proof: by
  rw [borel_eq_generateFrom_isClosed]
  refine MeasurableSpace.generateFrom_le fun t ht => μ.isCaratheodory_iff_le.2 fun s => ?_
  set S : Nat -> Set X := fun n => {x in s | (↑n)⁻¹ <= infEDist x t}
  have Ssep (n) : Metric.AreSeparated (S n) t :=
    ⟨n⁻¹, ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _),
fun x hx y hy => hx.2.trans infEDist_le_edist_of_mem hy⟩
  have Ssep' : forall n, Metric.AreSeparated (S n) (s inter t) := fun n =>
    (Ssep n).mono Subset.rfl inter_subset_right
  have S_sub : forall n, S n subseteq s \ t := fun n =>
    subset_inter inter_subset_left (Ssep n).subset_compl_right
  have hSs : forall n, μ (s inter t) + μ (S n) <= μ s := fun n =>
    calc
μ (s inter t) + μ (S n) = μ (s inter t union S n) := Eq.symm hm _ _ (Ssep' n).symm
_ <= μ (s inter t union s \ t) := μ.mono union_subset_union_right _ S_sub n
      _ = μ s := by rw [inter_union_sdiff]
  have iUnion_S : ⋃ n, S n = s \ t := by
    refine Subset.antisymm (iUnion_subset S_sub) ?_
    rintro x ⟨hxs, hxt⟩
    rw [mem_iff_infEDist_zero_of_closed ht] at hxt
    rcases ENNReal.exists_inv_nat_lt hxt with ⟨n, hn⟩
    exact mem_iUnion.2 ⟨n, hxs, hn.le⟩
  /- Now we have `∀ n, μ (s ∩ t) + μ (S n) ≤ μ s` and we need to prove
    `μ (s ∩ t) + μ (⋃ n, S n) ≤ μ s`. We can't pass to the limit because
    `μ` is only an outer measure. -/
  by_cases htop : μ (s \ t) = ∞
  · rw [htop, add_top, ← htop]
    exact μ.mono sdiff_subset
  suffices μ (⋃ n, S n) <= ⨆ n, μ (S n) by calc
    μ (s inter t) + μ (s \ t) = μ (s inter t) + μ (⋃ n, S n) := by rw [iUnion_S]
    _ <= μ (s inter t) + ⨆ n, μ (S n) := by gcongr
    _ = ⨆ n, μ (s inter t) + μ (S n) := ENNReal.add_iSup ..
    _ <= μ s := iSup_le hSs
  /- It suffices to show that `∑' k, μ (S (k + 1) \ S k) ≠ ∞`. Indeed, if we have this,
    then for all `N` we have `μ (⋃ n, S n) ≤ μ (S N) + ∑' k, m (S (N + k + 1) \ S (N + k))`
    and the second term tends to zero, see `OuterMeasure.iUnion_nat_of_monotone_of_tsum_ne_top`
    for details. -/
  have : forall n, S n subseteq S (n + 1) := fun n x hx =>
    ⟨hx.1, le_trans (ENNReal.inv_le_inv.2 <| Nat.cast_le.2 n.le_succ) hx.2⟩
  refine (μ.iUnion_nat_of_monotone_of_tsum_ne_top this ?_).le; clear this
  /- While the sets `S (k + 1) \ S k` are not pairwise metric separated, the sets in each
    subsequence `S (2 * k + 1) \ S (2 * k)` and `S (2 * k + 2) \ S (2 * k)` are metric separated,
    so `m` is additive on each of those sequences. -/
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]; rw [ENNReal.add_ne_top]
  suffices forall a, (∑' k : Nat, μ (S (2 * k + 1 + a) \ S (2 * k + a))) != ∞ from
    ⟨by simpa using this 0, by simpa using this 1⟩
  refine fun r => ne_top_of_le_ne_top htop ?_
  rw [← iUnion_S]; rw [ENNReal.tsum_eq_iSup_nat]; rw [iSup_le_iff]
  intro n
  rw [← hm.finset_iUnion_of_pairwise_separated]
  · exact μ.mono (iUnion_subset fun i => iUnion_subset fun _ x hx => mem_iUnion.2 ⟨_, hx.1⟩)
  suffices forall i j, i < j -> Metric.AreSeparated (S (2 * i + 1 + r)) (s \ S (2 * j + r)) from
    fun i _ j _ hij => hij.lt_or_gt.elim
      (fun h => (this i j h).mono inter_subset_left fun x hx => by exact ⟨hx.1.1, hx.2⟩)
      fun h => (this j i h).symm.mono (fun x hx => by exact ⟨hx.1.1, hx.2⟩) inter_subset_left
  intro i j hj
  have A : ((↑(2 * j + r))⁻¹ : Real>=0∞) < (↑(2 * i + 1 + r))⁻¹ := by
    rw [ENNReal.inv_lt_inv]; rw [Nat.cast_lt]; lia
  refine ⟨(↑(2 * i + 1 + r))⁻¹ - (↑(2 * j + r))⁻¹, by simpa [tsub_eq_zero_iff_le] using A,
    fun x hx y hy => ?_⟩
  have : infEDist y t < (↑(2 * j + r))⁻¹ := not_le.1 fun hle => hy.2 ⟨hy.1, hle⟩
  rcases infEDist_lt_iff.mp this with ⟨z, hzt, hyz⟩
  have hxz : (↑(2 * i + 1 + r))⁻¹ <= edist x z := le_infEDist.1 hx.2 _ hzt
  apply ENNReal.le_of_add_le_add_right hyz.ne_top
  refine le_trans ?_ (edist_triangle _ _ _)
  refine (add_le_add le_rfl hyz.le).trans (Eq.trans_le ?_ hxz)
  rw [tsub_add_cancel_of_le A.le]

中文:
定理 borel_le_caratheodory
  条件: (hm : IsMetric μ)
  结论: borel X <= μ.caratheodory
  证明: by
  rw [borel_eq_generateFrom_isClosed]
  refine MeasurableSpace.generateFrom_le fun t ht => μ.isCaratheodory_iff_le.2 fun s => ?_
  set S : Nat -> Set X := fun n => {x in s | (↑n)⁻¹ <= infEDist x t}
  have Ssep (n) : Metric.AreSeparated (S n) t :=
    ⟨n⁻¹, ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _),
fun x hx y hy => hx.2.trans infEDist_le_edist_of_mem hy⟩
  have Ssep' : forall n, Metric.AreSeparated (S n) (s inter t) := fun n =>
    (Ssep n).mono Subset.rfl inter_subset_right
  have S_sub : forall n, S n subseteq s \ t := fun n =>
    subset_inter inter_subset_left (Ssep n).subset_compl_right
  have hSs : forall n, μ (s inter t) + μ (S n) <= μ s := fun n =>
    calc
μ (s inter t) + μ (S n) = μ (s inter t union S n) := Eq.symm hm _ _ (Ssep' n).symm
_ <= μ (s inter t union s \ t) := μ.mono union_subset_union_right _ S_sub n
      _ = μ s := by rw [inter_union_sdiff]
  have iUnion_S : ⋃ n, S n = s \ t := by
    refine Subset.antisymm (iUnion_subset S_sub) ?_
    rintro x ⟨hxs, hxt⟩
    rw [mem_iff_infEDist_zero_of_closed ht] at hxt
    rcases ENNReal.exists_inv_nat_lt hxt with ⟨n, hn⟩
    exact mem_iUnion.2 ⟨n, hxs, hn.le⟩
  /- Now we have `∀ n, μ (s ∩ t) + μ (S n) ≤ μ s` and we need to prove
    `μ (s ∩ t) + μ (⋃ n, S n) ≤ μ s`. We can't pass to the limit because
    `μ` is only an outer measure. -/
  by_cases htop : μ (s \ t) = ∞
  · rw [htop, add_top, ← htop]
    exact μ.mono sdiff_subset
  suffices μ (⋃ n, S n) <= ⨆ n, μ (S n) by calc
    μ (s inter t) + μ (s \ t) = μ (s inter t) + μ (⋃ n, S n) := by rw [iUnion_S]
    _ <= μ (s inter t) + ⨆ n, μ (S n) := by gcongr
    _ = ⨆ n, μ (s inter t) + μ (S n) := ENNReal.add_iSup ..
    _ <= μ s := iSup_le hSs
  /- It suffices to show that `∑' k, μ (S (k + 1) \ S k) ≠ ∞`. Indeed, if we have this,
    then for all `N` we have `μ (⋃ n, S n) ≤ μ (S N) + ∑' k, m (S (N + k + 1) \ S (N + k))`
    and the second term tends to zero, see `OuterMeasure.iUnion_nat_of_monotone_of_tsum_ne_top`
    for details. -/
  have : forall n, S n subseteq S (n + 1) := fun n x hx =>
    ⟨hx.1, le_trans (ENNReal.inv_le_inv.2 <| Nat.cast_le.2 n.le_succ) hx.2⟩
  refine (μ.iUnion_nat_of_monotone_of_tsum_ne_top this ?_).le; clear this
  /- While the sets `S (k + 1) \ S k` are not pairwise metric separated, the sets in each
    subsequence `S (2 * k + 1) \ S (2 * k)` and `S (2 * k + 2) \ S (2 * k)` are metric separated,
    so `m` is additive on each of those sequences. -/
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]; rw [ENNReal.add_ne_top]
  suffices forall a, (∑' k : Nat, μ (S (2 * k + 1 + a) \ S (2 * k + a))) != ∞ from
    ⟨by simpa using this 0, by simpa using this 1⟩
  refine fun r => ne_top_of_le_ne_top htop ?_
  rw [← iUnion_S]; rw [ENNReal.tsum_eq_iSup_nat]; rw [iSup_le_iff]
  intro n
  rw [← hm.finset_iUnion_of_pairwise_separated]
  · exact μ.mono (iUnion_subset fun i => iUnion_subset fun _ x hx => mem_iUnion.2 ⟨_, hx.1⟩)
  suffices forall i j, i < j -> Metric.AreSeparated (S (2 * i + 1 + r)) (s \ S (2 * j + r)) from
    fun i _ j _ hij => hij.lt_or_gt.elim
      (fun h => (this i j h).mono inter_subset_left fun x hx => by exact ⟨hx.1.1, hx.2⟩)
      fun h => (this j i h).symm.mono (fun x hx => by exact ⟨hx.1.1, hx.2⟩) inter_subset_left
  intro i j hj
  have A : ((↑(2 * j + r))⁻¹ : Real>=0∞) < (↑(2 * i + 1 + r))⁻¹ := by
    rw [ENNReal.inv_lt_inv]; rw [Nat.cast_lt]; lia
  refine ⟨(↑(2 * i + 1 + r))⁻¹ - (↑(2 * j + r))⁻¹, by simpa [tsub_eq_zero_iff_le] using A,
    fun x hx y hy => ?_⟩
  have : infEDist y t < (↑(2 * j + r))⁻¹ := not_le.1 fun hle => hy.2 ⟨hy.1, hle⟩
  rcases infEDist_lt_iff.mp this with ⟨z, hzt, hyz⟩
  have hxz : (↑(2 * i + 1 + r))⁻¹ <= edist x z := le_infEDist.1 hx.2 _ hzt
  apply ENNReal.le_of_add_le_add_right hyz.ne_top
  refine le_trans ?_ (edist_triangle _ _ _)
  refine (add_le_add le_rfl hyz.le).trans (Eq.trans_le ?_ hxz)
  rw [tsub_add_cancel_of_le A.le]

Depends on / 依赖: AreSeparated, ENNReal, ENNReal.inv_ne_zero, ENNReal.natCast_ne_top, MeasurableSpace, MeasurableSpace.generateFrom_le, Metric, Metric.AreSeparated, S_sub, Subset, Subset.rfl, borel_eq_generateFrom_isClosed, generateFrom_le, infEDist, infEDist_le_edist_of_mem, inter_subset_right, inv_ne_zero, isCaratheodory_iff_le, natCast_ne_top
-/
theorem borel_le_caratheodory (hm : IsMetric μ) : borel X <= μ.caratheodory := by
  rw [borel_eq_generateFrom_isClosed]
  refine MeasurableSpace.generateFrom_le fun t ht => μ.isCaratheodory_iff_le.2 fun s => ?_
  set S : Nat -> Set X := fun n => {x in s | (↑n)⁻¹ <= infEDist x t}
  have Ssep (n) : Metric.AreSeparated (S n) t :=
    ⟨n⁻¹, ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _),
fun x hx y hy => hx.2.trans infEDist_le_edist_of_mem hy⟩
  have Ssep' : forall n, Metric.AreSeparated (S n) (s inter t) := fun n =>
    (Ssep n).mono Subset.rfl inter_subset_right
  have S_sub : forall n, S n subseteq s \ t := fun n =>
    subset_inter inter_subset_left (Ssep n).subset_compl_right
  have hSs : forall n, μ (s inter t) + μ (S n) <= μ s := fun n =>
    calc
μ (s inter t) + μ (S n) = μ (s inter t union S n) := Eq.symm hm _ _ (Ssep' n).symm
_ <= μ (s inter t union s \ t) := μ.mono union_subset_union_right _ S_sub n
      _ = μ s := by rw [inter_union_sdiff]
  have iUnion_S : ⋃ n, S n = s \ t := by
    refine Subset.antisymm (iUnion_subset S_sub) ?_
    rintro x ⟨hxs, hxt⟩
    rw [mem_iff_infEDist_zero_of_closed ht] at hxt
    rcases ENNReal.exists_inv_nat_lt hxt with ⟨n, hn⟩
    exact mem_iUnion.2 ⟨n, hxs, hn.le⟩
  /- Now we have `∀ n, μ (s ∩ t) + μ (S n) ≤ μ s` and we need to prove
    `μ (s ∩ t) + μ (⋃ n, S n) ≤ μ s`. We can't pass to the limit because
    `μ` is only an outer measure. -/
  by_cases htop : μ (s \ t) = ∞
  · rw [htop, add_top, ← htop]
    exact μ.mono sdiff_subset
  suffices μ (⋃ n, S n) <= ⨆ n, μ (S n) by calc
    μ (s inter t) + μ (s \ t) = μ (s inter t) + μ (⋃ n, S n) := by rw [iUnion_S]
    _ <= μ (s inter t) + ⨆ n, μ (S n) := by gcongr
    _ = ⨆ n, μ (s inter t) + μ (S n) := ENNReal.add_iSup ..
    _ <= μ s := iSup_le hSs
  /- It suffices to show that `∑' k, μ (S (k + 1) \ S k) ≠ ∞`. Indeed, if we have this,
    then for all `N` we have `μ (⋃ n, S n) ≤ μ (S N) + ∑' k, m (S (N + k + 1) \ S (N + k))`
    and the second term tends to zero, see `OuterMeasure.iUnion_nat_of_monotone_of_tsum_ne_top`
    for details. -/
  have : forall n, S n subseteq S (n + 1) := fun n x hx =>
    ⟨hx.1, le_trans (ENNReal.inv_le_inv.2 <| Nat.cast_le.2 n.le_succ) hx.2⟩
  refine (μ.iUnion_nat_of_monotone_of_tsum_ne_top this ?_).le; clear this
  /- While the sets `S (k + 1) \ S k` are not pairwise metric separated, the sets in each
    subsequence `S (2 * k + 1) \ S (2 * k)` and `S (2 * k + 2) \ S (2 * k)` are metric separated,
    so `m` is additive on each of those sequences. -/
  rw [← tsum_even_add_odd ENNReal.summable ENNReal.summable]; rw [ENNReal.add_ne_top]
  suffices forall a, (∑' k : Nat, μ (S (2 * k + 1 + a) \ S (2 * k + a))) != ∞ from
    ⟨by simpa using this 0, by simpa using this 1⟩
  refine fun r => ne_top_of_le_ne_top htop ?_
  rw [← iUnion_S]; rw [ENNReal.tsum_eq_iSup_nat]; rw [iSup_le_iff]
  intro n
  rw [← hm.finset_iUnion_of_pairwise_separated]
  · exact μ.mono (iUnion_subset fun i => iUnion_subset fun _ x hx => mem_iUnion.2 ⟨_, hx.1⟩)
  suffices forall i j, i < j -> Metric.AreSeparated (S (2 * i + 1 + r)) (s \ S (2 * j + r)) from
    fun i _ j _ hij => hij.lt_or_gt.elim
      (fun h => (this i j h).mono inter_subset_left fun x hx => by exact ⟨hx.1.1, hx.2⟩)
      fun h => (this j i h).symm.mono (fun x hx => by exact ⟨hx.1.1, hx.2⟩) inter_subset_left
  intro i j hj
  have A : ((↑(2 * j + r))⁻¹ : Real>=0∞) < (↑(2 * i + 1 + r))⁻¹ := by
    rw [ENNReal.inv_lt_inv]; rw [Nat.cast_lt]; lia
  refine ⟨(↑(2 * i + 1 + r))⁻¹ - (↑(2 * j + r))⁻¹, by simpa [tsub_eq_zero_iff_le] using A,
    fun x hx y hy => ?_⟩
  have : infEDist y t < (↑(2 * j + r))⁻¹ := not_le.1 fun hle => hy.2 ⟨hy.1, hle⟩
  rcases infEDist_lt_iff.mp this with ⟨z, hzt, hyz⟩
  have hxz : (↑(2 * i + 1 + r))⁻¹ <= edist x z := le_infEDist.1 hx.2 _ hzt
  apply ENNReal.le_of_add_le_add_right hyz.ne_top
  refine le_trans ?_ (edist_triangle _ _ _)
  refine (add_le_add le_rfl hyz.le).trans (Eq.trans_le ?_ hxz)
  rw [tsub_add_cancel_of_le A.le]

/--
theorem `le_caratheodory` / 定理 `le_caratheodory`

English:
theorem le_caratheodory
  given: [MeasurableSpace X] [BorelSpace X] (hm : IsMetric μ)
  proof: by
  rw [BorelSpace.measurable_eq (α := X)]
  exact hm.borel_le_caratheodory

中文:
定理 le_caratheodory
  条件: [可测空间 X] [Borel空间 X] (hm : IsMetric μ)
  证明: by
  rw [BorelSpace.measurable_eq (α := X)]
  exact hm.borel_le_caratheodory

Depends on / 依赖: BorelSpace, BorelSpace.measurable_eq, borel_le_caratheodory, hm.borel_le_caratheodory, measurable_eq
-/
theorem le_caratheodory [MeasurableSpace X] [BorelSpace X] (hm : IsMetric μ) :
    ‹MeasurableSpace X› <= μ.caratheodory := by
  rw [BorelSpace.measurable_eq (α := X)]
  exact hm.borel_le_caratheodory

end IsMetric

/-!
### Constructors of metric outer measures

In this section we provide constructors `MeasureTheory.OuterMeasure.mkMetric'` and
`MeasureTheory.OuterMeasure.mkMetric` and prove that these outer measures are metric outer
measures. We also prove basic lemmas about `map`/`comap` of these measures.
-/


/--
Definition of `mkMetric'.pre` / `mkMetric'.pre` 的定义

English:
definition mkMetric'.pre
  signature: (m : Set X -> Real>=0∞) (r : Real>=0∞)
  body: boundedBy extend fun s (_ : ediam s <= r) => m s

中文:
定义 mkMetric'.pre
  签名: (m : 集合 X -> 实数>=0∞) (r : 实数>=0∞)
  定义体: boundedBy extend fun s (_ : ediam s <= r) => m s

Depends on / 依赖: boundedBy, extend
-/
def mkMetric'.pre (m : Set X -> Real>=0∞) (r : Real>=0∞) : OuterMeasure X :=
boundedBy extend fun s (_ : ediam s <= r) => m s

/--
Definition of `mkMetric'` / `mkMetric'` 的定义

English:
definition mkMetric'
  signature: (m : Set X -> Real>=0∞)
  body: ⨆ r > 0, mkMetric'.pre m r

中文:
定义 mkMetric'
  签名: (m : 集合 X -> 实数>=0∞)
  定义体: ⨆ r > 0, mkMetric'.pre m r
-/
def mkMetric' (m : Set X -> Real>=0∞) : OuterMeasure X :=
  ⨆ r > 0, mkMetric'.pre m r

/--
Definition of `mkMetric` / `mkMetric` 的定义

English:
definition mkMetric
  signature: (m : Real>=0∞ -> Real>=0∞)
  body: mkMetric' fun s => m (ediam s)

中文:
定义 mkMetric
  签名: (m : 实数>=0∞ -> 实数>=0∞)
  定义体: mkMetric' fun s => m (ediam s)

Depends on / 依赖: mkMetric
-/
def mkMetric (m : Real>=0∞ -> Real>=0∞) : OuterMeasure X :=
  mkMetric' fun s => m (ediam s)

namespace mkMetric'

variable {m : Set X -> Real>=0∞} {r : Real>=0∞} {μ : OuterMeasure X} {s : Set X}

/--
theorem `le_pre` / 定理 `le_pre`

English:
theorem le_pre
  statement: μ <= pre m r ↔ forall s : Set X, ediam s <= r -> μ s <= m s
  proof: by
  simp only [pre, le_boundedBy, extend, le_iInf_iff]

中文:
定理 le_pre
  结论: μ <= pre m r ↔ 对任意 s : 集合 X, ediam s <= r -> μ s <= m s
  证明: by
  simp only [pre, le_boundedBy, extend, le_iInf_iff]

Depends on / 依赖: extend, le_boundedBy, le_iInf_iff
-/
theorem le_pre : μ <= pre m r ↔ forall s : Set X, ediam s <= r -> μ s <= m s := by
  simp only [pre, le_boundedBy, extend, le_iInf_iff]

/--
theorem `pre_le` / 定理 `pre_le`

English:
theorem pre_le
  given: (hs : ediam s <= r)
  statement: pre m r s <= m s
  proof: (boundedBy_le _).trans iInf_le _ hs

中文:
定理 pre_le
  条件: (hs : ediam s <= r)
  结论: pre m r s <= m s
  证明: (boundedBy_le _).trans iInf_le _ hs

Depends on / 依赖: boundedBy_le, iInf_le
-/
theorem pre_le (hs : ediam s <= r) : pre m r s <= m s :=
(boundedBy_le _).trans iInf_le _ hs

/--
theorem `mono_pre` / 定理 `mono_pre`

English:
theorem mono_pre
  given: (m : Set X -> Real>=0∞) {r r' : Real>=0∞} (h : r <= r')
  statement: pre m r' <= pre m r
  proof: le_pre.2 fun _ hs => pre_le (hs.trans h)

中文:
定理 mono_pre
  条件: (m : 集合 X -> 实数>=0∞) {r r' : 实数>=0∞} (h : r <= r')
  结论: pre m r' <= pre m r
  证明: le_pre.2 fun _ hs => pre_le (hs.trans h)

Depends on / 依赖: hs.trans, le_pre, pre_le
-/
theorem mono_pre (m : Set X -> Real>=0∞) {r r' : Real>=0∞} (h : r <= r') : pre m r' <= pre m r :=
  le_pre.2 fun _ hs => pre_le (hs.trans h)

/--
theorem `mono_pre_nat` / 定理 `mono_pre_nat`

English:
theorem mono_pre_nat
  given: (m : Set X -> Real>=0∞)
  statement: Monotone fun k : Nat => pre m k⁻¹
  proof: fun k l h => le_pre.2 fun _ hs => pre_le (hs.trans <| by simpa)

中文:
定理 mono_pre_nat
  条件: (m : 集合 X -> 实数>=0∞)
  结论: 递增 fun k : 自然数 => pre m k⁻¹
  证明: fun k l h => le_pre.2 fun _ hs => pre_le (hs.trans <| by simpa)

Depends on / 依赖: hs.trans, le_pre, pre_le
-/
theorem mono_pre_nat (m : Set X -> Real>=0∞) : Monotone fun k : Nat => pre m k⁻¹ :=
  fun k l h => le_pre.2 fun _ hs => pre_le (hs.trans <| by simpa)

/--
theorem `tendsto_pre` / 定理 `tendsto_pre`

English:
theorem tendsto_pre
  given: (m : Set X -> Real>=0∞) (s : Set X)
  proof: by
  rw [← tendsto_comp_coe_Ioi_atBot]
  simp only [mkMetric', OuterMeasure.iSup_apply, iSup_subtype']
  exact tendsto_atBot_iSup fun r r' hr => mono_pre _ hr _

中文:
定理 tendsto_pre
  条件: (m : 集合 X -> 实数>=0∞) (s : 集合 X)
  证明: by
  rw [← tendsto_comp_coe_Ioi_atBot]
  simp only [mkMetric', OuterMeasure.iSup_apply, iSup_subtype']
  exact tendsto_atBot_iSup fun r r' hr => mono_pre _ hr _

Depends on / 依赖: OuterMeasure, OuterMeasure.iSup_apply, iSup_apply, iSup_subtype, mkMetric, mono_pre, tendsto_atBot_iSup, tendsto_comp_coe_Ioi_atBot
-/
theorem tendsto_pre (m : Set X -> Real>=0∞) (s : Set X) :
    Tendsto (fun r => pre m r s) (𝓝[>] 0) (𝓝 <| mkMetric' m s) := by
  rw [← tendsto_comp_coe_Ioi_atBot]
  simp only [mkMetric', OuterMeasure.iSup_apply, iSup_subtype']
  exact tendsto_atBot_iSup fun r r' hr => mono_pre _ hr _

/--
theorem `tendsto_pre_nat` / 定理 `tendsto_pre_nat`

English:
theorem tendsto_pre_nat
  given: (m : Set X -> Real>=0∞) (s : Set X)
  proof: by
  refine (tendsto_pre m s).comp (tendsto_inf.2 ⟨ENNReal.tendsto_inv_nat_nhds_zero, ?_⟩)
  refine tendsto_principal.2 (Eventually.of_forall fun n => ?_)
  simp

中文:
定理 tendsto_pre_nat
  条件: (m : 集合 X -> 实数>=0∞) (s : 集合 X)
  证明: by
  refine (tendsto_pre m s).comp (tendsto_inf.2 ⟨ENNReal.tendsto_inv_nat_nhds_zero, ?_⟩)
  refine tendsto_principal.2 (Eventually.of_forall fun n => ?_)
  simp

Depends on / 依赖: ENNReal, ENNReal.tendsto_inv_nat_nhds_zero, Eventually, Eventually.of_forall, of_forall, tendsto_inf, tendsto_inv_nat_nhds_zero, tendsto_pre, tendsto_principal
-/
theorem tendsto_pre_nat (m : Set X -> Real>=0∞) (s : Set X) :
    Tendsto (fun n : Nat => pre m n⁻¹ s) atTop (𝓝 <| mkMetric' m s) := by
  refine (tendsto_pre m s).comp (tendsto_inf.2 ⟨ENNReal.tendsto_inv_nat_nhds_zero, ?_⟩)
  refine tendsto_principal.2 (Eventually.of_forall fun n => ?_)
  simp

/--
theorem `eq_iSup_nat` / 定理 `eq_iSup_nat`

English:
theorem eq_iSup_nat
  given: (m : Set X -> Real>=0∞)
  statement: mkMetric' m = ⨆ n : Nat, mkMetric'.pre m n⁻¹
  proof: by
  ext1 s
  rw [iSup_apply]
  refine tendsto_nhds_unique (mkMetric'.tendsto_pre_nat m s)
    (tendsto_atTop_iSup fun k l hkl => mkMetric'.mono_pre_nat m hkl s)

中文:
定理 eq_iSup_nat
  条件: (m : 集合 X -> 实数>=0∞)
  结论: mkMetric' m = ⨆ n : 自然数, mkMetric'.pre m n⁻¹
  证明: by
  ext1 s
  rw [iSup_apply]
  refine tendsto_nhds_unique (mkMetric'.tendsto_pre_nat m s)
    (tendsto_atTop_iSup fun k l hkl => mkMetric'.mono_pre_nat m hkl s)

Depends on / 依赖: iSup_apply, mkMetric, mono_pre_nat, tendsto_atTop_iSup, tendsto_nhds_unique, tendsto_pre_nat
-/
theorem eq_iSup_nat (m : Set X -> Real>=0∞) : mkMetric' m = ⨆ n : Nat, mkMetric'.pre m n⁻¹ := by
  ext1 s
  rw [iSup_apply]
  refine tendsto_nhds_unique (mkMetric'.tendsto_pre_nat m s)
    (tendsto_atTop_iSup fun k l hkl => mkMetric'.mono_pre_nat m hkl s)

/--
theorem `trim_pre` / 定理 `trim_pre`

English:
theorem trim_pre
  statement: [MeasurableSpace X] [OpensMeasurableSpace X] (m : Set X -> Real>=0∞)
  proof: by
  refine le_antisymm (le_pre.2 fun s hs => ?_) (le_trim _)
  rw [trim_eq_iInf]
refine iInf_le_of_le (closure s) iInf_le_of_le subset_closure
    iInf_le_of_le measurableSet_closure ((pre_le ?_).trans_eq (hcl _))
  rwa [ediam_closure]

中文:
定理 trim_pre
  结论: [可测空间 X] [OpensMeasurable空间 X] (m : 集合 X -> 实数>=0∞)
  证明: by
  refine le_antisymm (le_pre.2 fun s hs => ?_) (le_trim _)
  rw [trim_eq_iInf]
refine iInf_le_of_le (closure s) iInf_le_of_le subset_closure
    iInf_le_of_le measurableSet_closure ((pre_le ?_).trans_eq (hcl _))
  rwa [ediam_closure]

Depends on / 依赖: closure, ediam_closure, iInf_le_of_le, le_antisymm, le_pre, le_trim, measurableSet_closure, pre_le, subset_closure, trans_eq, trim_eq_iInf
-/
theorem trim_pre [MeasurableSpace X] [OpensMeasurableSpace X] (m : Set X -> Real>=0∞)
    (hcl : forall s, m (closure s) = m s) (r : Real>=0∞) : (pre m r).trim = pre m r := by
  refine le_antisymm (le_pre.2 fun s hs => ?_) (le_trim _)
  rw [trim_eq_iInf]
refine iInf_le_of_le (closure s) iInf_le_of_le subset_closure
    iInf_le_of_le measurableSet_closure ((pre_le ?_).trans_eq (hcl _))
  rwa [ediam_closure]

end mkMetric'

/--
theorem `mkMetric'_isMetric` / 定理 `mkMetric'_isMetric`

English:
theorem mkMetric'_isMetric
  given: (m : Set X -> Real>=0∞)
  statement: (mkMetric' m).IsMetric
  proof: by
  rintro s t ⟨r, r0, hr⟩
  refine tendsto_nhds_unique_of_eventuallyEq
    (mkMetric'.tendsto_pre _ _) ((mkMetric'.tendsto_pre _ _).add (mkMetric'.tendsto_pre _ _)) ?_
  rw [← pos_iff_ne_zero] at r0
  filter_upwards [Ioo_mem_nhdsGT r0]
  rintro ε ⟨_, εr⟩
  refine boundedBy_union_of_top_of_nonempty_inter ?_
  rintro u ⟨x, hxs, hxu⟩ ⟨y, hyt, hyu⟩
  have : ε < ediam u := εr.trans_le ((hr x hxs y hyt).trans <| edist_le_ediam_of_mem hxu hyu)
  exact iInf_eq_top.2 fun h => (this.not_ge h).elim

中文:
定理 mkMetric'_isMetric
  条件: (m : 集合 X -> 实数>=0∞)
  结论: (mkMetric' m).IsMetric
  证明: by
  rintro s t ⟨r, r0, hr⟩
  refine tendsto_nhds_unique_of_eventuallyEq
    (mkMetric'.tendsto_pre _ _) ((mkMetric'.tendsto_pre _ _).add (mkMetric'.tendsto_pre _ _)) ?_
  rw [← pos_iff_ne_zero] at r0
  filter_upwards [Ioo_mem_nhdsGT r0]
  rintro ε ⟨_, εr⟩
  refine boundedBy_union_of_top_of_nonempty_inter ?_
  rintro u ⟨x, hxs, hxu⟩ ⟨y, hyt, hyu⟩
  have : ε < ediam u := εr.trans_le ((hr x hxs y hyt).trans <| edist_le_ediam_of_mem hxu hyu)
  exact iInf_eq_top.2 fun h => (this.not_ge h).elim
-/
theorem mkMetric'_isMetric (m : Set X -> Real>=0∞) : (mkMetric' m).IsMetric := by
  rintro s t ⟨r, r0, hr⟩
  refine tendsto_nhds_unique_of_eventuallyEq
    (mkMetric'.tendsto_pre _ _) ((mkMetric'.tendsto_pre _ _).add (mkMetric'.tendsto_pre _ _)) ?_
  rw [← pos_iff_ne_zero] at r0
  filter_upwards [Ioo_mem_nhdsGT r0]
  rintro ε ⟨_, εr⟩
  refine boundedBy_union_of_top_of_nonempty_inter ?_
  rintro u ⟨x, hxs, hxu⟩ ⟨y, hyt, hyu⟩
  have : ε < ediam u := εr.trans_le ((hr x hxs y hyt).trans <| edist_le_ediam_of_mem hxu hyu)
  exact iInf_eq_top.2 fun h => (this.not_ge h).elim

/--
theorem `mkMetric_mono_smul` / 定理 `mkMetric_mono_smul`

English:
theorem mkMetric_mono_smul
  statement: {m₁ m₂ : Real>=0∞ -> Real>=0∞} {c : Real>=0∞} (hc : c != ∞) (h0 : c != 0)
  proof: by
  rcases (mem_nhdsGE_iff_exists_Ico_subset' zero_lt_one).1 hle with ⟨r, hr0, hr⟩
  refine fun s =>
    le_of_tendsto_of_tendsto (mkMetric'.tendsto_pre _ s)
      (ENNReal.Tendsto.const_mul (mkMetric'.tendsto_pre _ s) (Or.inr hc))
      (mem_of_superset (Ioo_mem_nhdsGT hr0) fun r' hr' => ?_)
  simp only [mem_ofPred_eq, mkMetric'.pre]
  rw [← smul_eq_mul]; rw [← smul_apply]; rw [smul_boundedBy hc]
  refine le_boundedBy.2 (fun t => (boundedBy_le _).trans ?_) _
  simp only [smul_eq_mul, Pi.smul_apply, extend, iInf_eq_if]
  split_ifs with ht
  · exact hr ⟨zero_le, ht.trans_lt hr'.2⟩
  · simp [h0]

@[simp]

中文:
定理 mkMetric_mono_smul
  结论: {m₁ m₂ : 实数>=0∞ -> 实数>=0∞} {c : 实数>=0∞} (hc : c != ∞) (h0 : c != 0)
  证明: by
  rcases (mem_nhdsGE_iff_exists_Ico_subset' zero_lt_one).1 hle with ⟨r, hr0, hr⟩
  refine fun s =>
    le_of_tendsto_of_tendsto (mkMetric'.tendsto_pre _ s)
      (ENNReal.Tendsto.const_mul (mkMetric'.tendsto_pre _ s) (Or.inr hc))
      (mem_of_superset (Ioo_mem_nhdsGT hr0) fun r' hr' => ?_)
  simp only [mem_ofPred_eq, mkMetric'.pre]
  rw [← smul_eq_mul]; rw [← smul_apply]; rw [smul_boundedBy hc]
  refine le_boundedBy.2 (fun t => (boundedBy_le _).trans ?_) _
  simp only [smul_eq_mul, Pi.smul_apply, extend, iInf_eq_if]
  split_ifs with ht
  · exact hr ⟨zero_le, ht.trans_lt hr'.2⟩
  · simp [h0]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.Tendsto.const_mul, Ioo_mem_nhdsGT, Or.inr, Pi.smul_apply, Tendsto, boundedBy_le, const_mul, extend, iInf_eq_if, le_boundedBy, le_of_tendsto_of_tendsto, mem_nhdsGE_iff_exists_Ico_subset, mem_ofPred_eq, mem_of_superset, mkMetric, smul_apply, smul_boundedBy, smul_eq_mul, tendsto_pre
-/
theorem mkMetric_mono_smul {m₁ m₂ : Real>=0∞ -> Real>=0∞} {c : Real>=0∞} (hc : c != ∞) (h0 : c != 0)
    (hle : m₁ <=ᶠ[𝓝[>=] 0] c • m₂) : (mkMetric m₁ : OuterMeasure X) <= c • mkMetric m₂ := by
  rcases (mem_nhdsGE_iff_exists_Ico_subset' zero_lt_one).1 hle with ⟨r, hr0, hr⟩
  refine fun s =>
    le_of_tendsto_of_tendsto (mkMetric'.tendsto_pre _ s)
      (ENNReal.Tendsto.const_mul (mkMetric'.tendsto_pre _ s) (Or.inr hc))
      (mem_of_superset (Ioo_mem_nhdsGT hr0) fun r' hr' => ?_)
  simp only [mem_ofPred_eq, mkMetric'.pre]
  rw [← smul_eq_mul]; rw [← smul_apply]; rw [smul_boundedBy hc]
  refine le_boundedBy.2 (fun t => (boundedBy_le _).trans ?_) _
  simp only [smul_eq_mul, Pi.smul_apply, extend, iInf_eq_if]
  split_ifs with ht
  · exact hr ⟨zero_le, ht.trans_lt hr'.2⟩
  · simp [h0]

@[simp]
/--
theorem `mkMetric_top` / 定理 `mkMetric_top`

English:
theorem mkMetric_top
  statement: (mkMetric (fun _ => ∞ : Real>=0∞ -> Real>=0∞) : OuterMeasure X) = ⊤
  proof: by
  simp_rw [mkMetric, mkMetric', mkMetric'.pre, extend_top, boundedBy_top, eq_top_iff]
  rw [le_iSup_iff]
  intro b hb
  simpa using hb ⊤

中文:
定理 mkMetric_top
  结论: (mkMetric (fun _ => ∞ : 实数>=0∞ -> 实数>=0∞) : 外测度 X) = ⊤
  证明: by
  simp_rw [mkMetric, mkMetric', mkMetric'.pre, extend_top, boundedBy_top, eq_top_iff]
  rw [le_iSup_iff]
  intro b hb
  simpa using hb ⊤

Depends on / 依赖: boundedBy_top, eq_top_iff, extend_top, le_iSup_iff, mkMetric, simp_rw
-/
theorem mkMetric_top : (mkMetric (fun _ => ∞ : Real>=0∞ -> Real>=0∞) : OuterMeasure X) = ⊤ := by
  simp_rw [mkMetric, mkMetric', mkMetric'.pre, extend_top, boundedBy_top, eq_top_iff]
  rw [le_iSup_iff]
  intro b hb
  simpa using hb ⊤

/--
theorem `mkMetric_mono` / 定理 `mkMetric_mono`

English:
theorem mkMetric_mono
  given: {m₁ m₂ : Real>=0∞ -> Real>=0∞} (hle : m₁ <=ᶠ[𝓝 0] m₂)
  proof: by
  convert! @mkMetric_mono_smul X _ _ m₂ _ ENNReal.one_ne_top one_ne_zero _ <;> simp [*]

中文:
定理 mkMetric_mono
  条件: {m₁ m₂ : 实数>=0∞ -> 实数>=0∞} (hle : m₁ <=ᶠ[𝓝 0] m₂)
  证明: by
  convert! @mkMetric_mono_smul X _ _ m₂ _ ENNReal.one_ne_top one_ne_zero _ <;> simp [*]

Depends on / 依赖: ENNReal, ENNReal.one_ne_top, convert, mkMetric_mono_smul, one_ne_top, one_ne_zero
-/
theorem mkMetric_mono {m₁ m₂ : Real>=0∞ -> Real>=0∞} (hle : m₁ <=ᶠ[𝓝 0] m₂) :
    (mkMetric m₁ : OuterMeasure X) <= mkMetric m₂ := by
  convert! @mkMetric_mono_smul X _ _ m₂ _ ENNReal.one_ne_top one_ne_zero _ <;> simp [*]

/--
theorem `isometry_comap_mkMetric` / 定理 `isometry_comap_mkMetric`

English:
theorem isometry_comap_mkMetric
  statement: (m : Real>=0∞ -> Real>=0∞) {f : X -> Y} (hf : Isometry f)
  proof: by
  simp only [mkMetric, mkMetric', mkMetric'.pre, comap_iSup]
  refine surjective_id.iSup_congr id fun ε => surjective_id.iSup_congr id fun hε => ?_
  rw [comap_boundedBy _ (H.imp _ id)]
  · congr with s : 1
    apply extend_congr <;> simp [hf.ediam_image]
  · intro h_mono s t hst
    simp only [extend, le_iInf_iff]
    intro ht
    apply le_trans _ (h_mono (ediam_mono hst))
    simp only [(ediam_mono hst).trans ht, le_refl, ciInf_pos]

中文:
定理 isometry_comap_mkMetric
  结论: (m : 实数>=0∞ -> 实数>=0∞) {f : X -> Y} (hf : 等距 f)
  证明: by
  simp only [mkMetric, mkMetric', mkMetric'.pre, comap_iSup]
  refine surjective_id.iSup_congr id fun ε => surjective_id.iSup_congr id fun hε => ?_
  rw [comap_boundedBy _ (H.imp _ id)]
  · congr with s : 1
    apply extend_congr <;> simp [hf.ediam_image]
  · intro h_mono s t hst
    simp only [extend, le_iInf_iff]
    intro ht
    apply le_trans _ (h_mono (ediam_mono hst))
    simp only [(ediam_mono hst).trans ht, le_refl, ciInf_pos]

Depends on / 依赖: H.imp, ciInf_pos, comap_boundedBy, comap_iSup, ediam_image, ediam_mono, extend, extend_congr, h_mono, hf.ediam_image, iSup_congr, le_iInf_iff, le_refl, le_trans, mkMetric, surjective_id, surjective_id.iSup_congr
-/
theorem isometry_comap_mkMetric (m : Real>=0∞ -> Real>=0∞) {f : X -> Y} (hf : Isometry f)
    (H : Monotone m ∨ Surjective f) : comap f (mkMetric m) = mkMetric m := by
  simp only [mkMetric, mkMetric', mkMetric'.pre, comap_iSup]
  refine surjective_id.iSup_congr id fun ε => surjective_id.iSup_congr id fun hε => ?_
  rw [comap_boundedBy _ (H.imp _ id)]
  · congr with s : 1
    apply extend_congr <;> simp [hf.ediam_image]
  · intro h_mono s t hst
    simp only [extend, le_iInf_iff]
    intro ht
    apply le_trans _ (h_mono (ediam_mono hst))
    simp only [(ediam_mono hst).trans ht, le_refl, ciInf_pos]

/--
theorem `mkMetric_smul` / 定理 `mkMetric_smul`

English:
theorem mkMetric_smul
  given: (m : Real>=0∞ -> Real>=0∞) {c : Real>=0∞} (hc : c != ∞) (hc' : c != 0)
  proof: by
  simp only [mkMetric, mkMetric', mkMetric'.pre]
  simp_rw [smul_iSup, smul_boundedBy hc, ennreal_smul_extend _ hc', Pi.smul_apply]

中文:
定理 mkMetric_smul
  条件: (m : 实数>=0∞ -> 实数>=0∞) {c : 实数>=0∞} (hc : c != ∞) (hc' : c != 0)
  证明: by
  simp only [mkMetric, mkMetric', mkMetric'.pre]
  simp_rw [smul_iSup, smul_boundedBy hc, ennreal_smul_extend _ hc', Pi.smul_apply]

Depends on / 依赖: Pi.smul_apply, ennreal_smul_extend, mkMetric, simp_rw, smul_apply, smul_boundedBy, smul_iSup
-/
theorem mkMetric_smul (m : Real>=0∞ -> Real>=0∞) {c : Real>=0∞} (hc : c != ∞) (hc' : c != 0) :
    (mkMetric (c • m) : OuterMeasure X) = c • mkMetric m := by
  simp only [mkMetric, mkMetric', mkMetric'.pre]
  simp_rw [smul_iSup, smul_boundedBy hc, ennreal_smul_extend _ hc', Pi.smul_apply]

/--
theorem `mkMetric_nnreal_smul` / 定理 `mkMetric_nnreal_smul`

English:
theorem mkMetric_nnreal_smul
  given: (m : Real>=0∞ -> Real>=0∞) {c : Real>=0} (hc : c != 0)
  proof: by
  rw [ENNReal.smul_def]; rw [ENNReal.smul_def]; rw [mkMetric_smul m ENNReal.coe_ne_top (ENNReal.coe_ne_zero.mpr hc)]

中文:
定理 mkMetric_nnreal_smul
  条件: (m : 实数>=0∞ -> 实数>=0∞) {c : 实数>=0} (hc : c != 0)
  证明: by
  rw [ENNReal.smul_def]; rw [ENNReal.smul_def]; rw [mkMetric_smul m ENNReal.coe_ne_top (ENNReal.coe_ne_zero.mpr hc)]

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, ENNReal.coe_ne_zero.mpr, ENNReal.smul_def, coe_ne_top, coe_ne_zero, mkMetric_smul, smul_def
-/
theorem mkMetric_nnreal_smul (m : Real>=0∞ -> Real>=0∞) {c : Real>=0} (hc : c != 0) :
    (mkMetric (c • m) : OuterMeasure X) = c • mkMetric m := by
  rw [ENNReal.smul_def]; rw [ENNReal.smul_def]; rw [mkMetric_smul m ENNReal.coe_ne_top (ENNReal.coe_ne_zero.mpr hc)]

/--
theorem `isometry_map_mkMetric` / 定理 `isometry_map_mkMetric`

English:
theorem isometry_map_mkMetric
  statement: (m : Real>=0∞ -> Real>=0∞) {f : X -> Y} (hf : Isometry f)
  proof: by
  rw [← isometry_comap_mkMetric _ hf H]; rw [map_comap]

中文:
定理 isometry_map_mkMetric
  结论: (m : 实数>=0∞ -> 实数>=0∞) {f : X -> Y} (hf : 等距 f)
  证明: by
  rw [← isometry_comap_mkMetric _ hf H]; rw [map_comap]

Depends on / 依赖: isometry_comap_mkMetric, map_comap
-/
theorem isometry_map_mkMetric (m : Real>=0∞ -> Real>=0∞) {f : X -> Y} (hf : Isometry f)
    (H : Monotone m ∨ Surjective f) : map f (mkMetric m) = restrict (range f) (mkMetric m) := by
  rw [← isometry_comap_mkMetric _ hf H]; rw [map_comap]

/--
theorem `isometryEquiv_comap_mkMetric` / 定理 `isometryEquiv_comap_mkMetric`

English:
theorem isometryEquiv_comap_mkMetric
  given: (m : Real>=0∞ -> Real>=0∞) (f : X ≃ᵢ Y)
  proof: isometry_comap_mkMetric _ f.isometry (Or.inr f.surjective)

中文:
定理 isometryEquiv_comap_mkMetric
  条件: (m : 实数>=0∞ -> 实数>=0∞) (f : X ≃ᵢ Y)
  证明: isometry_comap_mkMetric _ f.isometry (Or.inr f.surjective)

Depends on / 依赖: Or.inr, f.isometry, f.surjective, isometry, isometry_comap_mkMetric, surjective
-/
theorem isometryEquiv_comap_mkMetric (m : Real>=0∞ -> Real>=0∞) (f : X ≃ᵢ Y) :
    comap f (mkMetric m) = mkMetric m :=
  isometry_comap_mkMetric _ f.isometry (Or.inr f.surjective)

/--
theorem `isometryEquiv_map_mkMetric` / 定理 `isometryEquiv_map_mkMetric`

English:
theorem isometryEquiv_map_mkMetric
  given: (m : Real>=0∞ -> Real>=0∞) (f : X ≃ᵢ Y)
  proof: by
  rw [← isometryEquiv_comap_mkMetric _ f]; rw [map_comap_of_surjective f.surjective]

中文:
定理 isometryEquiv_map_mkMetric
  条件: (m : 实数>=0∞ -> 实数>=0∞) (f : X ≃ᵢ Y)
  证明: by
  rw [← isometryEquiv_comap_mkMetric _ f]; rw [map_comap_of_surjective f.surjective]

Depends on / 依赖: f.surjective, isometryEquiv_comap_mkMetric, map_comap_of_surjective, surjective
-/
theorem isometryEquiv_map_mkMetric (m : Real>=0∞ -> Real>=0∞) (f : X ≃ᵢ Y) :
    map f (mkMetric m) = mkMetric m := by
  rw [← isometryEquiv_comap_mkMetric _ f]; rw [map_comap_of_surjective f.surjective]

/--
theorem `trim_mkMetric` / 定理 `trim_mkMetric`

English:
theorem trim_mkMetric
  given: [MeasurableSpace X] [BorelSpace X] (m : Real>=0∞ -> Real>=0∞)
  proof: by
  simp only [mkMetric, mkMetric'.eq_iSup_nat, trim_iSup]
  congr 1 with n : 1
  refine mkMetric'.trim_pre _ (fun s => ?_) _
  simp

中文:
定理 trim_mkMetric
  条件: [可测空间 X] [Borel空间 X] (m : 实数>=0∞ -> 实数>=0∞)
  证明: by
  simp only [mkMetric, mkMetric'.eq_iSup_nat, trim_iSup]
  congr 1 with n : 1
  refine mkMetric'.trim_pre _ (fun s => ?_) _
  simp

Depends on / 依赖: eq_iSup_nat, mkMetric, trim_iSup, trim_pre
-/
theorem trim_mkMetric [MeasurableSpace X] [BorelSpace X] (m : Real>=0∞ -> Real>=0∞) :
    (mkMetric m : OuterMeasure X).trim = mkMetric m := by
  simp only [mkMetric, mkMetric'.eq_iSup_nat, trim_iSup]
  congr 1 with n : 1
  refine mkMetric'.trim_pre _ (fun s => ?_) _
  simp

/--
theorem `le_mkMetric` / 定理 `le_mkMetric`

English:
theorem le_mkMetric
  statement: (m : Real>=0∞ -> Real>=0∞) (μ : OuterMeasure X) (r : Real>=0∞) (h0 : 0 < r)
  proof: le_iSup₂_of_le r h0 mkMetric'.le_pre.2 fun _ hs => hr _ hs

中文:
定理 le_mkMetric
  结论: (m : 实数>=0∞ -> 实数>=0∞) (μ : 外测度 X) (r : 实数>=0∞) (h0 : 0 < r)
  证明: le_iSup₂_of_le r h0 mkMetric'.le_pre.2 fun _ hs => hr _ hs

Depends on / 依赖: le_pre, mkMetric
-/
theorem le_mkMetric (m : Real>=0∞ -> Real>=0∞) (μ : OuterMeasure X) (r : Real>=0∞) (h0 : 0 < r)
    (hr : forall s, ediam s <= r -> μ s <= m (ediam s)) : μ <= mkMetric m :=
le_iSup₂_of_le r h0 mkMetric'.le_pre.2 fun _ hs => hr _ hs

end OuterMeasure

/-!
### Metric measures

In this section we use `MeasureTheory.OuterMeasure.toMeasure` and theorems about
`MeasureTheory.OuterMeasure.mkMetric'`/`MeasureTheory.OuterMeasure.mkMetric` to define
`MeasureTheory.Measure.mkMetric'`/`MeasureTheory.Measure.mkMetric`. We also restate some lemmas
about metric outer measures for metric measures.
-/


namespace Measure

variable [MeasurableSpace X] [BorelSpace X]

/--
Definition of `mkMetric'` / `mkMetric'` 的定义

English:
definition mkMetric'
  signature: (m : Set X -> Real>=0∞)
  body: (OuterMeasure.mkMetric' m).toMeasure (OuterMeasure.mkMetric'_isMetric _).le_caratheodory

中文:
定义 mkMetric'
  签名: (m : 集合 X -> 实数>=0∞)
  定义体: (OuterMeasure.mkMetric' m).toMeasure (OuterMeasure.mkMetric'_isMetric _).le_caratheodory

Depends on / 依赖: OuterMeasure, OuterMeasure.mkMetric, _isMetric, le_caratheodory, mkMetric, toMeasure
-/
def mkMetric' (m : Set X -> Real>=0∞) : Measure X :=
  (OuterMeasure.mkMetric' m).toMeasure (OuterMeasure.mkMetric'_isMetric _).le_caratheodory

/--
Definition of `mkMetric` / `mkMetric` 的定义

English:
definition mkMetric
  signature: (m : Real>=0∞ -> Real>=0∞)
  body: (OuterMeasure.mkMetric m).toMeasure (OuterMeasure.mkMetric'_isMetric _).le_caratheodory

@[simp]

中文:
定义 mkMetric
  签名: (m : 实数>=0∞ -> 实数>=0∞)
  定义体: (OuterMeasure.mkMetric m).toMeasure (OuterMeasure.mkMetric'_isMetric _).le_caratheodory

@[simp]

Depends on / 依赖: OuterMeasure, OuterMeasure.mkMetric, _isMetric, le_caratheodory, mkMetric, toMeasure
-/
def mkMetric (m : Real>=0∞ -> Real>=0∞) : Measure X :=
  (OuterMeasure.mkMetric m).toMeasure (OuterMeasure.mkMetric'_isMetric _).le_caratheodory

@[simp]
/--
theorem `mkMetric'_toOuterMeasure` / 定理 `mkMetric'_toOuterMeasure`

English:
theorem mkMetric'_toOuterMeasure
  given: (m : Set X -> Real>=0∞)
  proof: rfl

@[simp]

中文:
定理 mkMetric'_toOuterMeasure
  条件: (m : 集合 X -> 实数>=0∞)
  证明: rfl

@[simp]
-/
theorem mkMetric'_toOuterMeasure (m : Set X -> Real>=0∞) :
    (mkMetric' m).toOuterMeasure = (OuterMeasure.mkMetric' m).trim :=
  rfl

@[simp]
/--
theorem `mkMetric_toOuterMeasure` / 定理 `mkMetric_toOuterMeasure`

English:
theorem mkMetric_toOuterMeasure
  given: (m : Real>=0∞ -> Real>=0∞)
  proof: OuterMeasure.trim_mkMetric m

中文:
定理 mkMetric_toOuterMeasure
  条件: (m : 实数>=0∞ -> 实数>=0∞)
  证明: OuterMeasure.trim_mkMetric m

Depends on / 依赖: OuterMeasure, OuterMeasure.trim_mkMetric, trim_mkMetric
-/
theorem mkMetric_toOuterMeasure (m : Real>=0∞ -> Real>=0∞) :
    (mkMetric m : Measure X).toOuterMeasure = OuterMeasure.mkMetric m :=
  OuterMeasure.trim_mkMetric m

end Measure

/--
theorem `OuterMeasure.coe_mkMetric` / 定理 `OuterMeasure.coe_mkMetric`

English:
theorem OuterMeasure.coe_mkMetric
  given: [MeasurableSpace X] [BorelSpace X] (m : Real>=0∞ -> Real>=0∞)
  proof: by
  rw [← Measure.mkMetric_toOuterMeasure]; rw [Measure.coe_toOuterMeasure]

中文:
定理 外测度.coe_mkMetric
  条件: [可测空间 X] [Borel空间 X] (m : 实数>=0∞ -> 实数>=0∞)
  证明: by
  rw [← Measure.mkMetric_toOuterMeasure]; rw [Measure.coe_toOuterMeasure]

Depends on / 依赖: Measure, Measure.coe_toOuterMeasure, Measure.mkMetric_toOuterMeasure, coe_toOuterMeasure, mkMetric_toOuterMeasure
-/
theorem OuterMeasure.coe_mkMetric [MeasurableSpace X] [BorelSpace X] (m : Real>=0∞ -> Real>=0∞) :
    ⇑(OuterMeasure.mkMetric m : OuterMeasure X) = Measure.mkMetric m := by
  rw [← Measure.mkMetric_toOuterMeasure]; rw [Measure.coe_toOuterMeasure]

namespace Measure

variable [MeasurableSpace X] [BorelSpace X]

/--
theorem `mkMetric_mono_smul` / 定理 `mkMetric_mono_smul`

English:
theorem mkMetric_mono_smul
  statement: {m₁ m₂ : Real>=0∞ -> Real>=0∞} {c : Real>=0∞} (hc : c != ∞) (h0 : c != 0)
  proof: fun s => by
  rw [← OuterMeasure.coe_mkMetric]; rw [coe_smul]; rw [← OuterMeasure.coe_mkMetric]
  exact OuterMeasure.mkMetric_mono_smul hc h0 hle s

@[simp]

中文:
定理 mkMetric_mono_smul
  结论: {m₁ m₂ : 实数>=0∞ -> 实数>=0∞} {c : 实数>=0∞} (hc : c != ∞) (h0 : c != 0)
  证明: fun s => by
  rw [← OuterMeasure.coe_mkMetric]; rw [coe_smul]; rw [← OuterMeasure.coe_mkMetric]
  exact OuterMeasure.mkMetric_mono_smul hc h0 hle s

@[simp]

Depends on / 依赖: OuterMeasure, OuterMeasure.coe_mkMetric, OuterMeasure.mkMetric_mono_smul, coe_mkMetric, coe_smul, mkMetric_mono_smul
-/
theorem mkMetric_mono_smul {m₁ m₂ : Real>=0∞ -> Real>=0∞} {c : Real>=0∞} (hc : c != ∞) (h0 : c != 0)
    (hle : m₁ <=ᶠ[𝓝[>=] 0] c • m₂) : (mkMetric m₁ : Measure X) <= c • mkMetric m₂ := fun s => by
  rw [← OuterMeasure.coe_mkMetric]; rw [coe_smul]; rw [← OuterMeasure.coe_mkMetric]
  exact OuterMeasure.mkMetric_mono_smul hc h0 hle s

@[simp]
/--
theorem `mkMetric_top` / 定理 `mkMetric_top`

English:
theorem mkMetric_top
  statement: (mkMetric (fun _ => ∞ : Real>=0∞ -> Real>=0∞) : Measure X) = ⊤
  proof: by
  apply toOuterMeasure_injective
  rw [mkMetric_toOuterMeasure]; rw [OuterMeasure.mkMetric_top]; rw [toOuterMeasure_top]

中文:
定理 mkMetric_top
  结论: (mkMetric (fun _ => ∞ : 实数>=0∞ -> 实数>=0∞) : 测度 X) = ⊤
  证明: by
  apply toOuterMeasure_injective
  rw [mkMetric_toOuterMeasure]; rw [OuterMeasure.mkMetric_top]; rw [toOuterMeasure_top]

Depends on / 依赖: OuterMeasure, OuterMeasure.mkMetric_top, mkMetric_toOuterMeasure, mkMetric_top, toOuterMeasure_injective, toOuterMeasure_top
-/
theorem mkMetric_top : (mkMetric (fun _ => ∞ : Real>=0∞ -> Real>=0∞) : Measure X) = ⊤ := by
  apply toOuterMeasure_injective
  rw [mkMetric_toOuterMeasure]; rw [OuterMeasure.mkMetric_top]; rw [toOuterMeasure_top]

/--
theorem `mkMetric_mono` / 定理 `mkMetric_mono`

English:
theorem mkMetric_mono
  given: {m₁ m₂ : Real>=0∞ -> Real>=0∞} (hle : m₁ <=ᶠ[𝓝 0] m₂)
  proof: by
  convert! @mkMetric_mono_smul X _ _ _ _ m₂ _ ENNReal.one_ne_top one_ne_zero _ <;> simp [*]

中文:
定理 mkMetric_mono
  条件: {m₁ m₂ : 实数>=0∞ -> 实数>=0∞} (hle : m₁ <=ᶠ[𝓝 0] m₂)
  证明: by
  convert! @mkMetric_mono_smul X _ _ _ _ m₂ _ ENNReal.one_ne_top one_ne_zero _ <;> simp [*]

Depends on / 依赖: ENNReal, ENNReal.one_ne_top, convert, mkMetric_mono_smul, one_ne_top, one_ne_zero
-/
theorem mkMetric_mono {m₁ m₂ : Real>=0∞ -> Real>=0∞} (hle : m₁ <=ᶠ[𝓝 0] m₂) :
    (mkMetric m₁ : Measure X) <= mkMetric m₂ := by
  convert! @mkMetric_mono_smul X _ _ _ _ m₂ _ ENNReal.one_ne_top one_ne_zero _ <;> simp [*]

/--
theorem `mkMetric_apply` / 定理 `mkMetric_apply`

English:
theorem mkMetric_apply
  given: (m : Real>=0∞ -> Real>=0∞) (s : Set X)
  proof: by
  classical
  -- We mostly unfold the definitions but we need to switch the order of `∑'` and `⨅`
  simp only [← OuterMeasure.coe_mkMetric, OuterMeasure.mkMetric, OuterMeasure.mkMetric',
    OuterMeasure.iSup_apply, OuterMeasure.mkMetric'.pre, OuterMeasure.boundedBy_apply, extend]
  refine
    surjective_id.iSup_congr id fun r =>
      iSup_congr_Prop Iff.rfl fun _ =>
        surjective_id.iInf_congr _ fun t => iInf_congr_Prop Iff.rfl fun ht => ?_
  dsimp
  by_cases htr : forall n, ediam (t n) <= r
  · rw [iInf_eq_if, if_pos htr]
    congr 1 with n : 1
    simp only [iInf_eq_if, htr n, if_true]
  · rw [iInf_eq_if, if_neg htr]
    push Not at htr; rcases htr with ⟨n, hn⟩
    refine ENNReal.tsum_eq_top_of_eq_top ⟨n, ?_⟩
    rw [iSup_eq_if]; rw [if_pos]; rw [iInf_eq_if]; rw [if_neg]
    · exact hn.not_ge
    rcases ediam_pos_iff.1 hn.pos with ⟨x, hx, -⟩
    exact ⟨x, hx⟩

中文:
定理 mkMetric_apply
  条件: (m : 实数>=0∞ -> 实数>=0∞) (s : 集合 X)
  证明: by
  classical
  -- We mostly unfold the definitions but we need to switch the order of `∑'` and `⨅`
  simp only [← OuterMeasure.coe_mkMetric, OuterMeasure.mkMetric, OuterMeasure.mkMetric',
    OuterMeasure.iSup_apply, OuterMeasure.mkMetric'.pre, OuterMeasure.boundedBy_apply, extend]
  refine
    surjective_id.iSup_congr id fun r =>
      iSup_congr_Prop Iff.rfl fun _ =>
        surjective_id.iInf_congr _ fun t => iInf_congr_Prop Iff.rfl fun ht => ?_
  dsimp
  by_cases htr : forall n, ediam (t n) <= r
  · rw [iInf_eq_if, if_pos htr]
    congr 1 with n : 1
    simp only [iInf_eq_if, htr n, if_true]
  · rw [iInf_eq_if, if_neg htr]
    push Not at htr; rcases htr with ⟨n, hn⟩
    refine ENNReal.tsum_eq_top_of_eq_top ⟨n, ?_⟩
    rw [iSup_eq_if]; rw [if_pos]; rw [iInf_eq_if]; rw [if_neg]
    · exact hn.not_ge
    rcases ediam_pos_iff.1 hn.pos with ⟨x, hx, -⟩
    exact ⟨x, hx⟩

Depends on / 依赖: classical
-/
theorem mkMetric_apply (m : Real>=0∞ -> Real>=0∞) (s : Set X) :
    mkMetric m s =
      ⨆ (r : Real>=0∞) (_ : 0 < r),
        ⨅ (t : Nat -> Set X) (_ : s subseteq iUnion t) (_ : forall n, ediam (t n) <= r),
          ∑' n, ⨆ _ : (t n).Nonempty, m (ediam (t n)) := by
  classical
  -- We mostly unfold the definitions but we need to switch the order of `∑'` and `⨅`
  simp only [← OuterMeasure.coe_mkMetric, OuterMeasure.mkMetric, OuterMeasure.mkMetric',
    OuterMeasure.iSup_apply, OuterMeasure.mkMetric'.pre, OuterMeasure.boundedBy_apply, extend]
  refine
    surjective_id.iSup_congr id fun r =>
      iSup_congr_Prop Iff.rfl fun _ =>
        surjective_id.iInf_congr _ fun t => iInf_congr_Prop Iff.rfl fun ht => ?_
  dsimp
  by_cases htr : forall n, ediam (t n) <= r
  · rw [iInf_eq_if, if_pos htr]
    congr 1 with n : 1
    simp only [iInf_eq_if, htr n, if_true]
  · rw [iInf_eq_if, if_neg htr]
    push Not at htr; rcases htr with ⟨n, hn⟩
    refine ENNReal.tsum_eq_top_of_eq_top ⟨n, ?_⟩
    rw [iSup_eq_if]; rw [if_pos]; rw [iInf_eq_if]; rw [if_neg]
    · exact hn.not_ge
    rcases ediam_pos_iff.1 hn.pos with ⟨x, hx, -⟩
    exact ⟨x, hx⟩

/--
theorem `le_mkMetric` / 定理 `le_mkMetric`

English:
theorem le_mkMetric
  statement: (m : Real>=0∞ -> Real>=0∞) (μ : Measure X) (ε : Real>=0∞) (h₀ : 0 < ε)
  proof: by
  rw [← toOuterMeasure_le]; rw [mkMetric_toOuterMeasure]
  exact OuterMeasure.le_mkMetric m μ.toOuterMeasure ε h₀ h

中文:
定理 le_mkMetric
  结论: (m : 实数>=0∞ -> 实数>=0∞) (μ : 测度 X) (ε : 实数>=0∞) (h₀ : 0 < ε)
  证明: by
  rw [← toOuterMeasure_le]; rw [mkMetric_toOuterMeasure]
  exact OuterMeasure.le_mkMetric m μ.toOuterMeasure ε h₀ h

Depends on / 依赖: OuterMeasure, OuterMeasure.le_mkMetric, le_mkMetric, mkMetric_toOuterMeasure, toOuterMeasure, toOuterMeasure_le
-/
theorem le_mkMetric (m : Real>=0∞ -> Real>=0∞) (μ : Measure X) (ε : Real>=0∞) (h₀ : 0 < ε)
    (h : forall s : Set X, ediam s <= ε -> μ s <= m (ediam s)) : μ <= mkMetric m := by
  rw [← toOuterMeasure_le]; rw [mkMetric_toOuterMeasure]
  exact OuterMeasure.le_mkMetric m μ.toOuterMeasure ε h₀ h

/--
theorem `mkMetric_le_liminf_tsum` / 定理 `mkMetric_le_liminf_tsum`

English:
theorem mkMetric_le_liminf_tsum
  statement: {β : Type*} {ι : β -> Type*} [forall n, Countable (ι n)] (s : Set X)
  proof: by
  have : forall n, Encodable (ι n) := fun n => Encodable.ofCountable _
  simp only [mkMetric_apply]
  refine iSup₂_le fun ε hε => ?_
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  rcases ((frequently_lt_of_liminf_lt (by isBoundedDefault) hc).and_eventually
        ((hr.eventually (gt_mem_nhds hε)).and (ht.and hst))).exists with
    ⟨n, hn, hrn, htn, hstn⟩
  set u : Nat -> Set X := fun j => ⋃ b in decode₂ (ι n) j, t n b
  refine iInf₂_le_of_le u (by rwa [iUnion_decode₂]) ?_
  refine iInf_le_of_le (fun j => ?_) ?_
  · rw [ediam_iUnion_mem_option]
    exact iSup₂_le fun _ _ => (htn _).trans hrn.le
  · calc
      (∑' j : Nat, ⨆ _ : (u j).Nonempty, m (ediam (u j))) = _ :=
        tsum_iUnion_decode₂ (fun t : Set X => ⨆ _ : t.Nonempty, m (ediam t)) (by simp) _
      _ <= ∑' i : ι n, m (ediam (t n i)) := ENNReal.tsum_le_tsum fun b => iSup_le fun _ => le_rfl
      _ <= c := hn.le

中文:
定理 mkMetric_le_liminf_tsum
  结论: {β : 类型} {ι : β -> 类型} [对任意 n, 可数 (ι n)] (s : 集合 X)
  证明: by
  have : forall n, Encodable (ι n) := fun n => Encodable.ofCountable _
  simp only [mkMetric_apply]
  refine iSup₂_le fun ε hε => ?_
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  rcases ((frequently_lt_of_liminf_lt (by isBoundedDefault) hc).and_eventually
        ((hr.eventually (gt_mem_nhds hε)).and (ht.and hst))).exists with
    ⟨n, hn, hrn, htn, hstn⟩
  set u : Nat -> Set X := fun j => ⋃ b in decode₂ (ι n) j, t n b
  refine iInf₂_le_of_le u (by rwa [iUnion_decode₂]) ?_
  refine iInf_le_of_le (fun j => ?_) ?_
  · rw [ediam_iUnion_mem_option]
    exact iSup₂_le fun _ _ => (htn _).trans hrn.le
  · calc
      (∑' j : Nat, ⨆ _ : (u j).Nonempty, m (ediam (u j))) = _ :=
        tsum_iUnion_decode₂ (fun t : Set X => ⨆ _ : t.Nonempty, m (ediam t)) (by simp) _
      _ <= ∑' i : ι n, m (ediam (t n i)) := ENNReal.tsum_le_tsum fun b => iSup_le fun _ => le_rfl
      _ <= c := hn.le

Depends on / 依赖: Encodable, Encodable.ofCountable, and_eventually, eventually, frequently_lt_of_liminf_lt, gt_mem_nhds, hr.eventually, ht.and, iInf_le_of_le, isBoundedDefault, le_of_forall_gt_imp_ge_of_dense, mkMetric_apply, ofCountable
-/
theorem mkMetric_le_liminf_tsum {β : Type*} {ι : β -> Type*} [forall n, Countable (ι n)] (s : Set X)
    {l : Filter β} (r : β -> Real>=0∞) (hr : Tendsto r l (𝓝 0)) (t : forall n : β, ι n -> Set X)
    (ht : forallᶠ n in l, forall i, ediam (t n i) <= r n) (hst : forallᶠ n in l, s subseteq ⋃ i, t n i) (m : Real>=0∞ -> Real>=0∞) :
    mkMetric m s <= liminf (fun n => ∑' i, m (ediam (t n i))) l := by
  have : forall n, Encodable (ι n) := fun n => Encodable.ofCountable _
  simp only [mkMetric_apply]
  refine iSup₂_le fun ε hε => ?_
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  rcases ((frequently_lt_of_liminf_lt (by isBoundedDefault) hc).and_eventually
        ((hr.eventually (gt_mem_nhds hε)).and (ht.and hst))).exists with
    ⟨n, hn, hrn, htn, hstn⟩
  set u : Nat -> Set X := fun j => ⋃ b in decode₂ (ι n) j, t n b
  refine iInf₂_le_of_le u (by rwa [iUnion_decode₂]) ?_
  refine iInf_le_of_le (fun j => ?_) ?_
  · rw [ediam_iUnion_mem_option]
    exact iSup₂_le fun _ _ => (htn _).trans hrn.le
  · calc
      (∑' j : Nat, ⨆ _ : (u j).Nonempty, m (ediam (u j))) = _ :=
        tsum_iUnion_decode₂ (fun t : Set X => ⨆ _ : t.Nonempty, m (ediam t)) (by simp) _
      _ <= ∑' i : ι n, m (ediam (t n i)) := ENNReal.tsum_le_tsum fun b => iSup_le fun _ => le_rfl
      _ <= c := hn.le

/--
theorem `mkMetric_le_liminf_sum` / 定理 `mkMetric_le_liminf_sum`

English:
theorem mkMetric_le_liminf_sum
  statement: {β : Type*} {ι : β -> Type*} [hι : forall n, Fintype (ι n)] (s : Set X)
  proof: by
  simpa only [tsum_fintype] using mkMetric_le_liminf_tsum s r hr t ht hst m

中文:
定理 mkMetric_le_liminf_sum
  结论: {β : 类型} {ι : β -> 类型} [hι : 对任意 n, 有限类型 (ι n)] (s : 集合 X)
  证明: by
  simpa only [tsum_fintype] using mkMetric_le_liminf_tsum s r hr t ht hst m

Depends on / 依赖: mkMetric_le_liminf_tsum, tsum_fintype
-/
theorem mkMetric_le_liminf_sum {β : Type*} {ι : β -> Type*} [hι : forall n, Fintype (ι n)] (s : Set X)
    {l : Filter β} (r : β -> Real>=0∞) (hr : Tendsto r l (𝓝 0)) (t : forall n : β, ι n -> Set X)
    (ht : forallᶠ n in l, forall i, ediam (t n i) <= r n) (hst : forallᶠ n in l, s subseteq ⋃ i, t n i) (m : Real>=0∞ -> Real>=0∞) :
    mkMetric m s <= liminf (fun n => ∑ i, m (ediam (t n i))) l := by
  simpa only [tsum_fintype] using mkMetric_le_liminf_tsum s r hr t ht hst m

/-!
### Hausdorff measure and Hausdorff dimension
-/


/--
Definition of `hausdorffMeasure` / `hausdorffMeasure` 的定义

English:
definition hausdorffMeasure
  signature: (d : Real)
  body: mkMetric fun r => r ^ d

@[inherit_doc]
scoped[MeasureTheory] notation "μH[" d "]" => MeasureTheory.Measure.hausdorffMeasure d

中文:
定义 hausdorffMeasure
  签名: (d : 实数)
  定义体: mkMetric fun r => r ^ d

@[inherit_doc]
scoped[MeasureTheory] notation "μH[" d "]" => MeasureTheory.Measure.hausdorffMeasure d

Depends on / 依赖: mkMetric
-/
def hausdorffMeasure (d : Real) : Measure X :=
  mkMetric fun r => r ^ d

@[inherit_doc]
scoped[MeasureTheory] notation "μH[" d "]" => MeasureTheory.Measure.hausdorffMeasure d

/--
theorem `le_hausdorffMeasure` / 定理 `le_hausdorffMeasure`

English:
theorem le_hausdorffMeasure
  statement: (d : Real) (μ : Measure X) (ε : Real>=0∞) (h₀ : 0 < ε)
  proof: le_mkMetric _ μ ε h₀ h

中文:
定理 le_hausdorffMeasure
  结论: (d : 实数) (μ : 测度 X) (ε : 实数>=0∞) (h₀ : 0 < ε)
  证明: le_mkMetric _ μ ε h₀ h

Depends on / 依赖: le_mkMetric
-/
theorem le_hausdorffMeasure (d : Real) (μ : Measure X) (ε : Real>=0∞) (h₀ : 0 < ε)
    (h : forall s : Set X, ediam s <= ε -> μ s <= ediam s ^ d) : μ <= μH[d] :=
  le_mkMetric _ μ ε h₀ h

/--
theorem `hausdorffMeasure_apply` / 定理 `hausdorffMeasure_apply`

English:
theorem hausdorffMeasure_apply
  given: (d : Real) (s : Set X)
  proof: mkMetric_apply _ _

中文:
定理 hausdorffMeasure_apply
  条件: (d : 实数) (s : 集合 X)
  证明: mkMetric_apply _ _

Depends on / 依赖: mkMetric_apply
-/
theorem hausdorffMeasure_apply (d : Real) (s : Set X) :
    μH[d] s =
      ⨆ (r : Real>=0∞) (_ : 0 < r),
        ⨅ (t : Nat -> Set X) (_ : s subseteq ⋃ n, t n) (_ : forall n, ediam (t n) <= r),
          ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ d :=
  mkMetric_apply _ _

/--
theorem `hausdorffMeasure_le_liminf_tsum` / 定理 `hausdorffMeasure_le_liminf_tsum`

English:
theorem hausdorffMeasure_le_liminf_tsum
  statement: {β : Type*} {ι : β -> Type*} [forall n, Countable (ι n)]
  proof: mkMetric_le_liminf_tsum s r hr t ht hst _

中文:
定理 hausdorffMeasure_le_liminf_tsum
  结论: {β : 类型} {ι : β -> 类型} [对任意 n, 可数 (ι n)]
  证明: mkMetric_le_liminf_tsum s r hr t ht hst _

Depends on / 依赖: mkMetric_le_liminf_tsum
-/
theorem hausdorffMeasure_le_liminf_tsum {β : Type*} {ι : β -> Type*} [forall n, Countable (ι n)]
    (d : Real) (s : Set X) {l : Filter β} (r : β -> Real>=0∞) (hr : Tendsto r l (𝓝 0))
    (t : forall n : β, ι n -> Set X) (ht : forallᶠ n in l, forall i, ediam (t n i) <= r n)
    (hst : forallᶠ n in l, s subseteq ⋃ i, t n i) : μH[d] s <= liminf (fun n => ∑' i, ediam (t n i) ^ d) l :=
  mkMetric_le_liminf_tsum s r hr t ht hst _

/--
theorem `hausdorffMeasure_le_liminf_sum` / 定理 `hausdorffMeasure_le_liminf_sum`

English:
theorem hausdorffMeasure_le_liminf_sum
  statement: {β : Type*} {ι : β -> Type*} [forall n, Fintype (ι n)]
  proof: mkMetric_le_liminf_sum s r hr t ht hst _

中文:
定理 hausdorffMeasure_le_liminf_sum
  结论: {β : 类型} {ι : β -> 类型} [对任意 n, 有限类型 (ι n)]
  证明: mkMetric_le_liminf_sum s r hr t ht hst _

Depends on / 依赖: mkMetric_le_liminf_sum
-/
theorem hausdorffMeasure_le_liminf_sum {β : Type*} {ι : β -> Type*} [forall n, Fintype (ι n)]
    (d : Real) (s : Set X) {l : Filter β} (r : β -> Real>=0∞) (hr : Tendsto r l (𝓝 0))
    (t : forall n : β, ι n -> Set X) (ht : forallᶠ n in l, forall i, ediam (t n i) <= r n)
    (hst : forallᶠ n in l, s subseteq ⋃ i, t n i) : μH[d] s <= liminf (fun n => ∑ i, ediam (t n i) ^ d) l :=
  mkMetric_le_liminf_sum s r hr t ht hst _

/--
theorem `hausdorffMeasure_zero_or_top` / 定理 `hausdorffMeasure_zero_or_top`

English:
theorem hausdorffMeasure_zero_or_top
  given: {d₁ d₂ : Real} (h : d₁ < d₂) (s : Set X)
  proof: by
  by_contra! H
  suffices forall c : Real>=0, c != 0 -> μH[d₂] s <= c * μH[d₁] s by
    rcases ENNReal.exists_nnreal_pos_mul_lt H.2 H.1 with ⟨c, hc0, hc⟩
    exact hc.not_ge (this c (pos_iff_ne_zero.1 hc0))
  intro c hc
  refine le_iff'.1 (mkMetric_mono_smul ENNReal.coe_ne_top (mod_cast hc) ?_) s
  have : 0 < ((c : Real>=0∞) ^ (d₂ - d₁)⁻¹) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hc]; rw [pos_iff_ne_zero]; rw [Ne]; rw [ENNReal.coe_eq_zero]; rw [NNReal.rpow_eq_zero_iff]
    exact mt And.left hc
  filter_upwards [Ico_mem_nhdsGE this]
  rintro r ⟨hr₀, hrc⟩
  lift r to Real>=0 using ne_top_of_lt hrc
  rw [Pi.smul_apply]; rw [smul_eq_mul]; rw [← ENNReal.div_le_iff_le_mul (Or.inr ENNReal.coe_ne_top) (Or.inr <| mt ENNReal.coe_eq_zero.1 hc)]
  rcases eq_or_ne r 0 with (rfl | hr₀)
  · rcases lt_or_ge 0 d₂ with (h₂ | h₂)
    · simp only [h₂, ENNReal.zero_rpow_of_pos, zero_le, ENNReal.zero_div, ENNReal.coe_zero]
    · simp only [h.trans_le h₂, ENNReal.div_top, zero_le, ENNReal.zero_rpow_of_neg,
        ENNReal.coe_zero]
  · have : (r : Real>=0∞) != 0 := by simpa only [ENNReal.coe_eq_zero, Ne] using hr₀
    rw [← ENNReal.rpow_sub _ _ this ENNReal.coe_ne_top]
    refine (ENNReal.rpow_lt_rpow hrc (sub_pos.2 h)).le.trans ?_
    rw [← ENNReal.rpow_mul]; rw [inv_mul_cancel₀ (sub_pos.2 h).ne']; rw [ENNReal.rpow_one]

中文:
定理 hausdorffMeasure_zero_or_top
  条件: {d₁ d₂ : 实数} (h : d₁ < d₂) (s : 集合 X)
  证明: by
  by_contra! H
  suffices forall c : Real>=0, c != 0 -> μH[d₂] s <= c * μH[d₁] s by
    rcases ENNReal.exists_nnreal_pos_mul_lt H.2 H.1 with ⟨c, hc0, hc⟩
    exact hc.not_ge (this c (pos_iff_ne_zero.1 hc0))
  intro c hc
  refine le_iff'.1 (mkMetric_mono_smul ENNReal.coe_ne_top (mod_cast hc) ?_) s
  have : 0 < ((c : Real>=0∞) ^ (d₂ - d₁)⁻¹) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hc]; rw [pos_iff_ne_zero]; rw [Ne]; rw [ENNReal.coe_eq_zero]; rw [NNReal.rpow_eq_zero_iff]
    exact mt And.left hc
  filter_upwards [Ico_mem_nhdsGE this]
  rintro r ⟨hr₀, hrc⟩
  lift r to Real>=0 using ne_top_of_lt hrc
  rw [Pi.smul_apply]; rw [smul_eq_mul]; rw [← ENNReal.div_le_iff_le_mul (Or.inr ENNReal.coe_ne_top) (Or.inr <| mt ENNReal.coe_eq_zero.1 hc)]
  rcases eq_or_ne r 0 with (rfl | hr₀)
  · rcases lt_or_ge 0 d₂ with (h₂ | h₂)
    · simp only [h₂, ENNReal.zero_rpow_of_pos, zero_le, ENNReal.zero_div, ENNReal.coe_zero]
    · simp only [h.trans_le h₂, ENNReal.div_top, zero_le, ENNReal.zero_rpow_of_neg,
        ENNReal.coe_zero]
  · have : (r : Real>=0∞) != 0 := by simpa only [ENNReal.coe_eq_zero, Ne] using hr₀
    rw [← ENNReal.rpow_sub _ _ this ENNReal.coe_ne_top]
    refine (ENNReal.rpow_lt_rpow hrc (sub_pos.2 h)).le.trans ?_
    rw [← ENNReal.rpow_mul]; rw [inv_mul_cancel₀ (sub_pos.2 h).ne']; rw [ENNReal.rpow_one]

Depends on / 依赖: And.left, ENNReal, ENNReal.coe_eq_zero, ENNReal.coe_ne_top, ENNReal.coe_rpow_of_ne_zero, ENNReal.exists_nnreal_pos_mul_lt, Ico_m, NNReal, NNReal.rpow_eq_zero_iff, coe_eq_zero, coe_ne_top, coe_rpow_of_ne_zero, exists_nnreal_pos_mul_lt, filter_upwards, hc.not_ge, le_iff, mkMetric_mono_smul, mod_cast, not_ge, pos_iff_ne_zero
-/
theorem hausdorffMeasure_zero_or_top {d₁ d₂ : Real} (h : d₁ < d₂) (s : Set X) :
    μH[d₂] s = 0 ∨ μH[d₁] s = ∞ := by
  by_contra! H
  suffices forall c : Real>=0, c != 0 -> μH[d₂] s <= c * μH[d₁] s by
    rcases ENNReal.exists_nnreal_pos_mul_lt H.2 H.1 with ⟨c, hc0, hc⟩
    exact hc.not_ge (this c (pos_iff_ne_zero.1 hc0))
  intro c hc
  refine le_iff'.1 (mkMetric_mono_smul ENNReal.coe_ne_top (mod_cast hc) ?_) s
  have : 0 < ((c : Real>=0∞) ^ (d₂ - d₁)⁻¹) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hc]; rw [pos_iff_ne_zero]; rw [Ne]; rw [ENNReal.coe_eq_zero]; rw [NNReal.rpow_eq_zero_iff]
    exact mt And.left hc
  filter_upwards [Ico_mem_nhdsGE this]
  rintro r ⟨hr₀, hrc⟩
  lift r to Real>=0 using ne_top_of_lt hrc
  rw [Pi.smul_apply]; rw [smul_eq_mul]; rw [← ENNReal.div_le_iff_le_mul (Or.inr ENNReal.coe_ne_top) (Or.inr <| mt ENNReal.coe_eq_zero.1 hc)]
  rcases eq_or_ne r 0 with (rfl | hr₀)
  · rcases lt_or_ge 0 d₂ with (h₂ | h₂)
    · simp only [h₂, ENNReal.zero_rpow_of_pos, zero_le, ENNReal.zero_div, ENNReal.coe_zero]
    · simp only [h.trans_le h₂, ENNReal.div_top, zero_le, ENNReal.zero_rpow_of_neg,
        ENNReal.coe_zero]
  · have : (r : Real>=0∞) != 0 := by simpa only [ENNReal.coe_eq_zero, Ne] using hr₀
    rw [← ENNReal.rpow_sub _ _ this ENNReal.coe_ne_top]
    refine (ENNReal.rpow_lt_rpow hrc (sub_pos.2 h)).le.trans ?_
    rw [← ENNReal.rpow_mul]; rw [inv_mul_cancel₀ (sub_pos.2 h).ne']; rw [ENNReal.rpow_one]

/--
theorem `hausdorffMeasure_mono` / 定理 `hausdorffMeasure_mono`

English:
theorem hausdorffMeasure_mono
  given: {d₁ d₂ : Real} (h : d₁ <= d₂) (s : Set X)
  statement: μH[d₂] s <= μH[d₁] s
  proof: by
  rcases h.eq_or_lt with (rfl | h); · exact le_rfl
  rcases hausdorffMeasure_zero_or_top h s with hs | hs <;> simp [hs]

中文:
定理 hausdorffMeasure_mono
  条件: {d₁ d₂ : 实数} (h : d₁ <= d₂) (s : 集合 X)
  结论: μH[d₂] s <= μH[d₁] s
  证明: by
  rcases h.eq_or_lt with (rfl | h); · exact le_rfl
  rcases hausdorffMeasure_zero_or_top h s with hs | hs <;> simp [hs]

Depends on / 依赖: eq_or_lt, h.eq_or_lt, hausdorffMeasure_zero_or_top, le_rfl
-/
theorem hausdorffMeasure_mono {d₁ d₂ : Real} (h : d₁ <= d₂) (s : Set X) : μH[d₂] s <= μH[d₁] s := by
  rcases h.eq_or_lt with (rfl | h); · exact le_rfl
  rcases hausdorffMeasure_zero_or_top h s with hs | hs <;> simp [hs]

variable (X) in
/--
theorem `nullSingletonClass_hausdorff` / 定理 `nullSingletonClass_hausdorff`

English:
theorem nullSingletonClass_hausdorff
  given: {d : Real} (hd : 0 < d)
  proof: by
  refine ⟨fun x => ?_⟩
  rw [← nonpos_iff_eq_zero]; rw [hausdorffMeasure_apply]
refine iSup₂_le fun ε _ => iInf₂_le_of_le (fun _ => {x}) ?_ iInf_le_of_le (fun _ => ?_) ?_
  · exact subset_iUnion (fun _ => {x} : Nat -> Set X) 0
  · simp only [ediam_singleton, zero_le]
  · simp [hd]

@[deprecated (since := "2026-06-09")]
alias noAtoms_hausdorff := nullSingletonClass_hausdorff

@[simp]

中文:
定理 nullSingletonClass_hausdorff
  条件: {d : 实数} (hd : 0 < d)
  证明: by
  refine ⟨fun x => ?_⟩
  rw [← nonpos_iff_eq_zero]; rw [hausdorffMeasure_apply]
refine iSup₂_le fun ε _ => iInf₂_le_of_le (fun _ => {x}) ?_ iInf_le_of_le (fun _ => ?_) ?_
  · exact subset_iUnion (fun _ => {x} : Nat -> Set X) 0
  · simp only [ediam_singleton, zero_le]
  · simp [hd]

@[deprecated (since := "2026-06-09")]
alias noAtoms_hausdorff := nullSingletonClass_hausdorff

@[simp]

Depends on / 依赖: ediam_singleton, hausdorffMeasure_apply, iInf_le_of_le, nonpos_iff_eq_zero, subset_iUnion, zero_le
-/
theorem nullSingletonClass_hausdorff {d : Real} (hd : 0 < d) :
    NullSingletonClass (hausdorffMeasure d : Measure X) := by
  refine ⟨fun x => ?_⟩
  rw [← nonpos_iff_eq_zero]; rw [hausdorffMeasure_apply]
refine iSup₂_le fun ε _ => iInf₂_le_of_le (fun _ => {x}) ?_ iInf_le_of_le (fun _ => ?_) ?_
  · exact subset_iUnion (fun _ => {x} : Nat -> Set X) 0
  · simp only [ediam_singleton, zero_le]
  · simp [hd]

@[deprecated (since := "2026-06-09")]
alias noAtoms_hausdorff := nullSingletonClass_hausdorff

@[simp]
/--
theorem `hausdorffMeasure_zero_singleton` / 定理 `hausdorffMeasure_zero_singleton`

English:
theorem hausdorffMeasure_zero_singleton
  given: (x : X)
  statement: μH[0] ({x} : Set X) = 1
  proof: by
  apply le_antisymm
  · let r : Nat -> Real>=0∞ := fun _ => 0
    let t : Nat -> Unit -> Set X := fun _ _ => {x}
    have ht : forallᶠ n in atTop, forall i, ediam (t n i) <= r n := by
      simp only [t, r, imp_true_iff, ediam_singleton, eventually_atTop,
        nonpos_iff_eq_zero, exists_const]
    simpa [t, liminf_const] using hausdorffMeasure_le_liminf_sum 0 {x} r tendsto_const_nhds t ht
  · rw [hausdorffMeasure_apply]
    suffices
      (1 : Real>=0∞) <=
        ⨅ (t : Nat -> Set X) (_ : {x} subseteq ⋃ n, t n) (_ : forall n, ediam (t n) <= 1),
          ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (0 : Real) by
      apply le_trans this _
      convert! le_iSup₂ (α := Real>=0∞) (1 : Real>=0∞) zero_lt_one
      rfl
    simp only [ENNReal.rpow_zero, le_iInf_iff]
    intro t hst _
    rcases mem_iUnion.1 (hst (mem_singleton x)) with ⟨m, hm⟩
    have A : (t m).Nonempty := ⟨x, hm⟩
    calc
      (1 : Real>=0∞) = ⨆ h : (t m).Nonempty, 1 := by simp only [A, ciSup_pos]
      _ <= ∑' n, ⨆ h : (t n).Nonempty, 1 := ENNReal.le_tsum _

中文:
定理 hausdorffMeasure_zero_singleton
  条件: (x : X)
  结论: μH[0] ({x} : 集合 X) = 1
  证明: by
  apply le_antisymm
  · let r : Nat -> Real>=0∞ := fun _ => 0
    let t : Nat -> Unit -> Set X := fun _ _ => {x}
    have ht : forallᶠ n in atTop, forall i, ediam (t n i) <= r n := by
      simp only [t, r, imp_true_iff, ediam_singleton, eventually_atTop,
        nonpos_iff_eq_zero, exists_const]
    simpa [t, liminf_const] using hausdorffMeasure_le_liminf_sum 0 {x} r tendsto_const_nhds t ht
  · rw [hausdorffMeasure_apply]
    suffices
      (1 : Real>=0∞) <=
        ⨅ (t : Nat -> Set X) (_ : {x} subseteq ⋃ n, t n) (_ : forall n, ediam (t n) <= 1),
          ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (0 : Real) by
      apply le_trans this _
      convert! le_iSup₂ (α := Real>=0∞) (1 : Real>=0∞) zero_lt_one
      rfl
    simp only [ENNReal.rpow_zero, le_iInf_iff]
    intro t hst _
    rcases mem_iUnion.1 (hst (mem_singleton x)) with ⟨m, hm⟩
    have A : (t m).Nonempty := ⟨x, hm⟩
    calc
      (1 : Real>=0∞) = ⨆ h : (t m).Nonempty, 1 := by simp only [A, ciSup_pos]
      _ <= ∑' n, ⨆ h : (t n).Nonempty, 1 := ENNReal.le_tsum _

Depends on / 依赖: ediam_singleton, eventually_atTop, exists_const, hausdorffMeasure_apply, hausdorffMeasure_le_liminf_sum, imp_true_iff, le_antisymm, liminf_const, nonpos_iff_eq_zero, subseteq, tendsto_const_nhds
-/
theorem hausdorffMeasure_zero_singleton (x : X) : μH[0] ({x} : Set X) = 1 := by
  apply le_antisymm
  · let r : Nat -> Real>=0∞ := fun _ => 0
    let t : Nat -> Unit -> Set X := fun _ _ => {x}
    have ht : forallᶠ n in atTop, forall i, ediam (t n i) <= r n := by
      simp only [t, r, imp_true_iff, ediam_singleton, eventually_atTop,
        nonpos_iff_eq_zero, exists_const]
    simpa [t, liminf_const] using hausdorffMeasure_le_liminf_sum 0 {x} r tendsto_const_nhds t ht
  · rw [hausdorffMeasure_apply]
    suffices
      (1 : Real>=0∞) <=
        ⨅ (t : Nat -> Set X) (_ : {x} subseteq ⋃ n, t n) (_ : forall n, ediam (t n) <= 1),
          ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ (0 : Real) by
      apply le_trans this _
      convert! le_iSup₂ (α := Real>=0∞) (1 : Real>=0∞) zero_lt_one
      rfl
    simp only [ENNReal.rpow_zero, le_iInf_iff]
    intro t hst _
    rcases mem_iUnion.1 (hst (mem_singleton x)) with ⟨m, hm⟩
    have A : (t m).Nonempty := ⟨x, hm⟩
    calc
      (1 : Real>=0∞) = ⨆ h : (t m).Nonempty, 1 := by simp only [A, ciSup_pos]
      _ <= ∑' n, ⨆ h : (t n).Nonempty, 1 := ENNReal.le_tsum _

/--
theorem `one_le_hausdorffMeasure_zero_of_nonempty` / 定理 `one_le_hausdorffMeasure_zero_of_nonempty`

English:
theorem one_le_hausdorffMeasure_zero_of_nonempty
  given: {s : Set X} (h : s.Nonempty)
  statement: 1 <= μH[0] s
  proof: by
  rcases h with ⟨x, hx⟩
  calc
    (1 : Real>=0∞) = μH[0] ({x} : Set X) := (hausdorffMeasure_zero_singleton x).symm
    _ <= μH[0] s := measure_mono (singleton_subset_iff.2 hx)

中文:
定理 one_le_hausdorffMeasure_zero_of_nonempty
  条件: {s : 集合 X} (h : s.非空)
  结论: 1 <= μH[0] s
  证明: by
  rcases h with ⟨x, hx⟩
  calc
    (1 : Real>=0∞) = μH[0] ({x} : Set X) := (hausdorffMeasure_zero_singleton x).symm
    _ <= μH[0] s := measure_mono (singleton_subset_iff.2 hx)

Depends on / 依赖: hausdorffMeasure_zero_singleton, measure_mono, singleton_subset_iff
-/
theorem one_le_hausdorffMeasure_zero_of_nonempty {s : Set X} (h : s.Nonempty) : 1 <= μH[0] s := by
  rcases h with ⟨x, hx⟩
  calc
    (1 : Real>=0∞) = μH[0] ({x} : Set X) := (hausdorffMeasure_zero_singleton x).symm
    _ <= μH[0] s := measure_mono (singleton_subset_iff.2 hx)

/--
theorem `hausdorffMeasure_le_one_of_subsingleton` / 定理 `hausdorffMeasure_le_one_of_subsingleton`

English:
theorem hausdorffMeasure_le_one_of_subsingleton
  statement: {s : Set X} (hs : s.Subsingleton) {d : Real}
  proof: by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
  · simp only [measure_empty, zero_le]
  · rw [(subsingleton_iff_singleton hx).1 hs]
    rcases eq_or_lt_of_le hd with (rfl | dpos)
    · simp only [le_refl, hausdorffMeasure_zero_singleton]
    · have := nullSingletonClass_hausdorff X dpos
      simp only [zero_le, measure_singleton]

中文:
定理 hausdorffMeasure_le_one_of_subsingleton
  结论: {s : 集合 X} (hs : s.子单例) {d : 实数}
  证明: by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
  · simp only [measure_empty, zero_le]
  · rw [(subsingleton_iff_singleton hx).1 hs]
    rcases eq_or_lt_of_le hd with (rfl | dpos)
    · simp only [le_refl, hausdorffMeasure_zero_singleton]
    · have := nullSingletonClass_hausdorff X dpos
      simp only [zero_le, measure_singleton]

Depends on / 依赖: eq_empty_or_nonempty, eq_or_lt_of_le, hausdorffMeasure_zero_singleton, le_refl, measure_empty, measure_singleton, nullSingletonClass_hausdorff, subsingleton_iff_singleton, zero_le
-/
theorem hausdorffMeasure_le_one_of_subsingleton {s : Set X} (hs : s.Subsingleton) {d : Real}
    (hd : 0 <= d) : μH[d] s <= 1 := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
  · simp only [measure_empty, zero_le]
  · rw [(subsingleton_iff_singleton hx).1 hs]
    rcases eq_or_lt_of_le hd with (rfl | dpos)
    · simp only [le_refl, hausdorffMeasure_zero_singleton]
    · have := nullSingletonClass_hausdorff X dpos
      simp only [zero_le, measure_singleton]

end Measure

end MeasureTheory

/-!
### Hausdorff measure, Hausdorff dimension, and Hölder or Lipschitz continuous maps
-/


open scoped MeasureTheory

open MeasureTheory MeasureTheory.Measure

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

namespace HolderOnWith

variable {C r : Real>=0} {f : X -> Y} {s : Set X}

/--
theorem `hausdorffMeasure_image_le` / 定理 `hausdorffMeasure_image_le`

English:
theorem hausdorffMeasure_image_le
  given: (h : HolderOnWith C r f s) (hr : 0 < r) {d : Real} (hd : 0 <= d)
  proof: by
  -- We start with the trivial case `C = 0`
  rcases eq_zero_or_pos C with (rfl | hC0)
  · rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
    · simp only [measure_empty, nonpos_iff_eq_zero, mul_zero, image_empty]
    have : f '' s = {f x} :=
      have : (f '' s).Subsingleton := by simpa [ediam_eq_zero_iff] using h.ediam_image_le
      (subsingleton_iff_singleton (mem_image_of_mem f hx)).1 this
    rw [this]
    rcases eq_or_lt_of_le hd with (rfl | h'd)
    · simp only [ENNReal.rpow_zero, one_mul, mul_zero]
      rw [hausdorffMeasure_zero_singleton]
      exact one_le_hausdorffMeasure_zero_of_nonempty ⟨x, hx⟩
    · have := nullSingletonClass_hausdorff Y h'd
      simp only [zero_le, measure_singleton]
  -- Now assume `C ≠ 0`
  · have hCd0 : (C : Real>=0∞) ^ d != 0 := by simp [hC0.ne']
    have hCd : (C : Real>=0∞) ^ d != ∞ := by simp [hd]
    simp only [hausdorffMeasure_apply, ENNReal.mul_iSup, ENNReal.mul_iInf_of_ne hCd0 hCd,
      ← ENNReal.tsum_mul_left]
    refine iSup_le fun R => iSup_le fun hR => ?_
    have : Tendsto (fun d : Real>=0∞ => (C : Real>=0∞) * d ^ (r : Real)) (𝓝 0) (𝓝 0) :=
      ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.coe_ne_top hr
    rcases ENNReal.nhds_zero_basis_Iic.eventually_iff.1 (this.eventually (gt_mem_nhds hR)) with
      ⟨δ, δ0, H⟩
refine le_iSup₂_of_le δ δ0 iInf₂_mono' fun t hst =>
      ⟨fun n => f '' (t n inter s), ?_, iInf_mono' fun htδ =>
        ⟨fun n => (h.ediam_image_inter_le (t n)).trans (H (htδ n)).le, ?_⟩⟩
    · grw [← image_iUnion, ← iUnion_inter, ← hst, inter_self]
    · refine ENNReal.tsum_le_tsum fun n => ?_
      simp only [iSup_le_iff, image_nonempty]
      intro hft
      simp only [Nonempty.mono ((t n).inter_subset_left) hft, ciSup_pos]
      rw [ENNReal.rpow_mul]; rw [← ENNReal.mul_rpow_of_nonneg _ _ hd]
      gcongr
      exact h.ediam_image_inter_le _

中文:
定理 hausdorffMeasure_image_le
  条件: (h : HolderOnWith C r f s) (hr : 0 < r) {d : 实数} (hd : 0 <= d)
  证明: by
  -- We start with the trivial case `C = 0`
  rcases eq_zero_or_pos C with (rfl | hC0)
  · rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
    · simp only [measure_empty, nonpos_iff_eq_zero, mul_zero, image_empty]
    have : f '' s = {f x} :=
      have : (f '' s).Subsingleton := by simpa [ediam_eq_zero_iff] using h.ediam_image_le
      (subsingleton_iff_singleton (mem_image_of_mem f hx)).1 this
    rw [this]
    rcases eq_or_lt_of_le hd with (rfl | h'd)
    · simp only [ENNReal.rpow_zero, one_mul, mul_zero]
      rw [hausdorffMeasure_zero_singleton]
      exact one_le_hausdorffMeasure_zero_of_nonempty ⟨x, hx⟩
    · have := nullSingletonClass_hausdorff Y h'd
      simp only [zero_le, measure_singleton]
  -- Now assume `C ≠ 0`
  · have hCd0 : (C : Real>=0∞) ^ d != 0 := by simp [hC0.ne']
    have hCd : (C : Real>=0∞) ^ d != ∞ := by simp [hd]
    simp only [hausdorffMeasure_apply, ENNReal.mul_iSup, ENNReal.mul_iInf_of_ne hCd0 hCd,
      ← ENNReal.tsum_mul_left]
    refine iSup_le fun R => iSup_le fun hR => ?_
    have : Tendsto (fun d : Real>=0∞ => (C : Real>=0∞) * d ^ (r : Real)) (𝓝 0) (𝓝 0) :=
      ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.coe_ne_top hr
    rcases ENNReal.nhds_zero_basis_Iic.eventually_iff.1 (this.eventually (gt_mem_nhds hR)) with
      ⟨δ, δ0, H⟩
refine le_iSup₂_of_le δ δ0 iInf₂_mono' fun t hst =>
      ⟨fun n => f '' (t n inter s), ?_, iInf_mono' fun htδ =>
        ⟨fun n => (h.ediam_image_inter_le (t n)).trans (H (htδ n)).le, ?_⟩⟩
    · grw [← image_iUnion, ← iUnion_inter, ← hst, inter_self]
    · refine ENNReal.tsum_le_tsum fun n => ?_
      simp only [iSup_le_iff, image_nonempty]
      intro hft
      simp only [Nonempty.mono ((t n).inter_subset_left) hft, ciSup_pos]
      rw [ENNReal.rpow_mul]; rw [← ENNReal.mul_rpow_of_nonneg _ _ hd]
      gcongr
      exact h.ediam_image_inter_le _
-/
theorem hausdorffMeasure_image_le (h : HolderOnWith C r f s) (hr : 0 < r) {d : Real} (hd : 0 <= d) :
    μH[d] (f '' s) <= (C : Real>=0∞) ^ d * μH[r * d] s := by
  -- We start with the trivial case `C = 0`
  rcases eq_zero_or_pos C with (rfl | hC0)
  · rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
    · simp only [measure_empty, nonpos_iff_eq_zero, mul_zero, image_empty]
    have : f '' s = {f x} :=
      have : (f '' s).Subsingleton := by simpa [ediam_eq_zero_iff] using h.ediam_image_le
      (subsingleton_iff_singleton (mem_image_of_mem f hx)).1 this
    rw [this]
    rcases eq_or_lt_of_le hd with (rfl | h'd)
    · simp only [ENNReal.rpow_zero, one_mul, mul_zero]
      rw [hausdorffMeasure_zero_singleton]
      exact one_le_hausdorffMeasure_zero_of_nonempty ⟨x, hx⟩
    · have := nullSingletonClass_hausdorff Y h'd
      simp only [zero_le, measure_singleton]
  -- Now assume `C ≠ 0`
  · have hCd0 : (C : Real>=0∞) ^ d != 0 := by simp [hC0.ne']
    have hCd : (C : Real>=0∞) ^ d != ∞ := by simp [hd]
    simp only [hausdorffMeasure_apply, ENNReal.mul_iSup, ENNReal.mul_iInf_of_ne hCd0 hCd,
      ← ENNReal.tsum_mul_left]
    refine iSup_le fun R => iSup_le fun hR => ?_
    have : Tendsto (fun d : Real>=0∞ => (C : Real>=0∞) * d ^ (r : Real)) (𝓝 0) (𝓝 0) :=
      ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.coe_ne_top hr
    rcases ENNReal.nhds_zero_basis_Iic.eventually_iff.1 (this.eventually (gt_mem_nhds hR)) with
      ⟨δ, δ0, H⟩
refine le_iSup₂_of_le δ δ0 iInf₂_mono' fun t hst =>
      ⟨fun n => f '' (t n inter s), ?_, iInf_mono' fun htδ =>
        ⟨fun n => (h.ediam_image_inter_le (t n)).trans (H (htδ n)).le, ?_⟩⟩
    · grw [← image_iUnion, ← iUnion_inter, ← hst, inter_self]
    · refine ENNReal.tsum_le_tsum fun n => ?_
      simp only [iSup_le_iff, image_nonempty]
      intro hft
      simp only [Nonempty.mono ((t n).inter_subset_left) hft, ciSup_pos]
      rw [ENNReal.rpow_mul]; rw [← ENNReal.mul_rpow_of_nonneg _ _ hd]
      gcongr
      exact h.ediam_image_inter_le _

end HolderOnWith

namespace LipschitzOnWith

open Submodule

variable {K : Real>=0} {f : X -> Y} {s : Set X}

/--
theorem `hausdorffMeasure_image_le` / 定理 `hausdorffMeasure_image_le`

English:
theorem hausdorffMeasure_image_le
  given: (h : LipschitzOnWith K f s) {d : Real} (hd : 0 <= d)
  proof: by
  simpa only [NNReal.coe_one, one_mul] using h.holderOnWith.hausdorffMeasure_image_le zero_lt_one hd

中文:
定理 hausdorffMeasure_image_le
  条件: (h : LipschitzOnWith K f s) {d : 实数} (hd : 0 <= d)
  证明: by
  simpa only [NNReal.coe_one, one_mul] using h.holderOnWith.hausdorffMeasure_image_le zero_lt_one hd

Depends on / 依赖: NNReal, NNReal.coe_one, coe_one, h.holderOnWith.hausdorffMeasure_image_le, hausdorffMeasure_image_le, holderOnWith, one_mul, zero_lt_one
-/
theorem hausdorffMeasure_image_le (h : LipschitzOnWith K f s) {d : Real} (hd : 0 <= d) :
    μH[d] (f '' s) <= (K : Real>=0∞) ^ d * μH[d] s := by
  simpa only [NNReal.coe_one, one_mul] using h.holderOnWith.hausdorffMeasure_image_le zero_lt_one hd

end LipschitzOnWith

namespace LipschitzWith

variable {K : Real>=0} {f : X -> Y}

/--
theorem `hausdorffMeasure_image_le` / 定理 `hausdorffMeasure_image_le`

English:
theorem hausdorffMeasure_image_le
  given: (h : LipschitzWith K f) {d : Real} (hd : 0 <= d) (s : Set X)
  proof: h.lipschitzOnWith.hausdorffMeasure_image_le hd

中文:
定理 hausdorffMeasure_image_le
  条件: (h : LipschitzWith K f) {d : 实数} (hd : 0 <= d) (s : 集合 X)
  证明: h.lipschitzOnWith.hausdorffMeasure_image_le hd

Depends on / 依赖: h.lipschitzOnWith.hausdorffMeasure_image_le, hausdorffMeasure_image_le, lipschitzOnWith
-/
theorem hausdorffMeasure_image_le (h : LipschitzWith K f) {d : Real} (hd : 0 <= d) (s : Set X) :
    μH[d] (f '' s) <= (K : Real>=0∞) ^ d * μH[d] s :=
  h.lipschitzOnWith.hausdorffMeasure_image_le hd

end LipschitzWith

open scoped Pointwise

/--
theorem `MeasureTheory.Measure.hausdorffMeasure_smul₀` / 定理 `MeasureTheory.Measure.hausdorffMeasure_smul₀`

English:
theorem MeasureTheory.Measure.hausdorffMeasure_smul₀
  statement: {𝕜 E : Type*} [NormedAddCommGroup E]
  proof: by
  have {r : 𝕜} (s : Set E) : μH[d] (r • s) <= ‖r‖₊ ^ d • μH[d] s := by
    simpa [ENNReal.coe_rpow_of_nonneg, hd]
      using (lipschitzWith_smul r).hausdorffMeasure_image_le hd s
  refine le_antisymm (this s) ?_
  rw [← le_inv_smul_iff_of_pos]
  · dsimp
    rw [← NNReal.inv_rpow]; rw [← nnnorm_inv]
    · refine Eq.trans_le ?_ (this (r • s))
      rw [inv_smul_smul₀ hr]
  · simp [pos_iff_ne_zero, hr]

中文:
定理 测度论.测度.hausdorffMeasure_smul₀
  结论: {𝕜 E : 类型} [赋范交换加群 E]
  证明: by
  have {r : 𝕜} (s : Set E) : μH[d] (r • s) <= ‖r‖₊ ^ d • μH[d] s := by
    simpa [ENNReal.coe_rpow_of_nonneg, hd]
      using (lipschitzWith_smul r).hausdorffMeasure_image_le hd s
  refine le_antisymm (this s) ?_
  rw [← le_inv_smul_iff_of_pos]
  · dsimp
    rw [← NNReal.inv_rpow]; rw [← nnnorm_inv]
    · refine Eq.trans_le ?_ (this (r • s))
      rw [inv_smul_smul₀ hr]
  · simp [pos_iff_ne_zero, hr]

Depends on / 依赖: ENNReal, ENNReal.coe_rpow_of_nonneg, Eq.trans_le, NNReal, NNReal.inv_rpow, coe_rpow_of_nonneg, hausdorffMeasure_image_le, inv_rpow, le_antisymm, le_inv_smul_iff_of_pos, lipschitzWith_smul, nnnorm_inv, pos_iff_ne_zero, trans_le
-/
theorem MeasureTheory.Measure.hausdorffMeasure_smul₀ {𝕜 E : Type*} [NormedAddCommGroup E]
    [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E] [MeasurableSpace E] [BorelSpace E]
    {d : Real} (hd : 0 <= d) {r : 𝕜} (hr : r != 0) (s : Set E) :
    μH[d] (r • s) = ‖r‖₊ ^ d • μH[d] s := by
  have {r : 𝕜} (s : Set E) : μH[d] (r • s) <= ‖r‖₊ ^ d • μH[d] s := by
    simpa [ENNReal.coe_rpow_of_nonneg, hd]
      using (lipschitzWith_smul r).hausdorffMeasure_image_le hd s
  refine le_antisymm (this s) ?_
  rw [← le_inv_smul_iff_of_pos]
  · dsimp
    rw [← NNReal.inv_rpow]; rw [← nnnorm_inv]
    · refine Eq.trans_le ?_ (this (r • s))
      rw [inv_smul_smul₀ hr]
  · simp [pos_iff_ne_zero, hr]

/-!
### Antilipschitz maps do not decrease Hausdorff measures and dimension
-/

namespace AntilipschitzWith

variable {f : X -> Y} {K : Real>=0} {d : Real}

/--
theorem `hausdorffMeasure_preimage_le` / 定理 `hausdorffMeasure_preimage_le`

English:
theorem hausdorffMeasure_preimage_le
  given: (hf : AntilipschitzWith K f) (hd : 0 <= d) (s : Set Y)
  proof: by
  rcases eq_or_ne K 0 with (rfl | h0)
  · rcases eq_empty_or_nonempty (f ⁻¹' s) with (hs | ⟨x, hx⟩)
    · simp only [hs, measure_empty, zero_le]
    have : f ⁻¹' s = {x} := by
      have : Subsingleton X := hf.subsingleton
      have : (f ⁻¹' s).Subsingleton := subsingleton_univ.anti (subset_univ _)
      exact (subsingleton_iff_singleton hx).1 this
    rw [this]
    rcases eq_or_lt_of_le hd with (rfl | h'd)
    · simp only [ENNReal.rpow_zero, one_mul]
      rw [hausdorffMeasure_zero_singleton]
      exact one_le_hausdorffMeasure_zero_of_nonempty ⟨f x, hx⟩
    · have := nullSingletonClass_hausdorff X h'd
      simp only [zero_le, measure_singleton]
  have hKd0 : (K : Real>=0∞) ^ d != 0 := by simp [h0]
  have hKd : (K : Real>=0∞) ^ d != ∞ := by simp [hd]
  simp only [hausdorffMeasure_apply, ENNReal.mul_iSup, ENNReal.mul_iInf_of_ne hKd0 hKd,
    ← ENNReal.tsum_mul_left]
  refine iSup₂_le fun ε ε0 => ?_
  refine le_iSup₂_of_le (ε / K) (by simp [ε0.ne']) ?_
  refine le_iInf₂ fun t hst => le_iInf fun htε => ?_
  replace hst : f ⁻¹' s subseteq _ := preimage_mono hst; rw [preimage_iUnion] at hst
  refine iInf₂_le_of_le _ hst (iInf_le_of_le (fun n => ?_) ?_)
  · exact (hf.ediam_preimage_le _).trans (ENNReal.mul_le_of_le_div' <| htε n)
  · refine ENNReal.tsum_le_tsum fun n => iSup_le_iff.2 fun hft => ?_
    simp only [nonempty_of_nonempty_preimage hft, ciSup_pos]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hd]
    exact ENNReal.rpow_le_rpow (hf.ediam_preimage_le _) hd

中文:
定理 hausdorffMeasure_preimage_le
  条件: (hf : AntilipschitzWith K f) (hd : 0 <= d) (s : 集合 Y)
  证明: by
  rcases eq_or_ne K 0 with (rfl | h0)
  · rcases eq_empty_or_nonempty (f ⁻¹' s) with (hs | ⟨x, hx⟩)
    · simp only [hs, measure_empty, zero_le]
    have : f ⁻¹' s = {x} := by
      have : Subsingleton X := hf.subsingleton
      have : (f ⁻¹' s).Subsingleton := subsingleton_univ.anti (subset_univ _)
      exact (subsingleton_iff_singleton hx).1 this
    rw [this]
    rcases eq_or_lt_of_le hd with (rfl | h'd)
    · simp only [ENNReal.rpow_zero, one_mul]
      rw [hausdorffMeasure_zero_singleton]
      exact one_le_hausdorffMeasure_zero_of_nonempty ⟨f x, hx⟩
    · have := nullSingletonClass_hausdorff X h'd
      simp only [zero_le, measure_singleton]
  have hKd0 : (K : Real>=0∞) ^ d != 0 := by simp [h0]
  have hKd : (K : Real>=0∞) ^ d != ∞ := by simp [hd]
  simp only [hausdorffMeasure_apply, ENNReal.mul_iSup, ENNReal.mul_iInf_of_ne hKd0 hKd,
    ← ENNReal.tsum_mul_left]
  refine iSup₂_le fun ε ε0 => ?_
  refine le_iSup₂_of_le (ε / K) (by simp [ε0.ne']) ?_
  refine le_iInf₂ fun t hst => le_iInf fun htε => ?_
  replace hst : f ⁻¹' s subseteq _ := preimage_mono hst; rw [preimage_iUnion] at hst
  refine iInf₂_le_of_le _ hst (iInf_le_of_le (fun n => ?_) ?_)
  · exact (hf.ediam_preimage_le _).trans (ENNReal.mul_le_of_le_div' <| htε n)
  · refine ENNReal.tsum_le_tsum fun n => iSup_le_iff.2 fun hft => ?_
    simp only [nonempty_of_nonempty_preimage hft, ciSup_pos]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hd]
    exact ENNReal.rpow_le_rpow (hf.ediam_preimage_le _) hd

Depends on / 依赖: ENNReal, ENNReal.rpow_zero, Subsingleton, eq_empty_or_nonempty, eq_or_lt_of_le, eq_or_ne, hausdorffMeasure_zero_singleton, hf.subsingleton, measure_empty, one_le_hausdorffMeasure_zero_of_nonempt, one_mul, rpow_zero, subset_univ, subsingleton, subsingleton_iff_singleton, subsingleton_univ, subsingleton_univ.anti, zero_le
-/
theorem hausdorffMeasure_preimage_le (hf : AntilipschitzWith K f) (hd : 0 <= d) (s : Set Y) :
    μH[d] (f ⁻¹' s) <= (K : Real>=0∞) ^ d * μH[d] s := by
  rcases eq_or_ne K 0 with (rfl | h0)
  · rcases eq_empty_or_nonempty (f ⁻¹' s) with (hs | ⟨x, hx⟩)
    · simp only [hs, measure_empty, zero_le]
    have : f ⁻¹' s = {x} := by
      have : Subsingleton X := hf.subsingleton
      have : (f ⁻¹' s).Subsingleton := subsingleton_univ.anti (subset_univ _)
      exact (subsingleton_iff_singleton hx).1 this
    rw [this]
    rcases eq_or_lt_of_le hd with (rfl | h'd)
    · simp only [ENNReal.rpow_zero, one_mul]
      rw [hausdorffMeasure_zero_singleton]
      exact one_le_hausdorffMeasure_zero_of_nonempty ⟨f x, hx⟩
    · have := nullSingletonClass_hausdorff X h'd
      simp only [zero_le, measure_singleton]
  have hKd0 : (K : Real>=0∞) ^ d != 0 := by simp [h0]
  have hKd : (K : Real>=0∞) ^ d != ∞ := by simp [hd]
  simp only [hausdorffMeasure_apply, ENNReal.mul_iSup, ENNReal.mul_iInf_of_ne hKd0 hKd,
    ← ENNReal.tsum_mul_left]
  refine iSup₂_le fun ε ε0 => ?_
  refine le_iSup₂_of_le (ε / K) (by simp [ε0.ne']) ?_
  refine le_iInf₂ fun t hst => le_iInf fun htε => ?_
  replace hst : f ⁻¹' s subseteq _ := preimage_mono hst; rw [preimage_iUnion] at hst
  refine iInf₂_le_of_le _ hst (iInf_le_of_le (fun n => ?_) ?_)
  · exact (hf.ediam_preimage_le _).trans (ENNReal.mul_le_of_le_div' <| htε n)
  · refine ENNReal.tsum_le_tsum fun n => iSup_le_iff.2 fun hft => ?_
    simp only [nonempty_of_nonempty_preimage hft, ciSup_pos]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hd]
    exact ENNReal.rpow_le_rpow (hf.ediam_preimage_le _) hd

/--
theorem `le_hausdorffMeasure_image` / 定理 `le_hausdorffMeasure_image`

English:
theorem le_hausdorffMeasure_image
  given: (hf : AntilipschitzWith K f) (hd : 0 <= d) (s : Set X)
  proof: calc
    μH[d] s <= μH[d] (f ⁻¹' f '' s) := measure_mono (subset_preimage_image _ _)
    _ <= (K : Real>=0∞) ^ d * μH[d] (f '' s) := hf.hausdorffMeasure_preimage_le hd (f '' s)

中文:
定理 le_hausdorffMeasure_image
  条件: (hf : AntilipschitzWith K f) (hd : 0 <= d) (s : 集合 X)
  证明: calc
    μH[d] s <= μH[d] (f ⁻¹' f '' s) := measure_mono (subset_preimage_image _ _)
    _ <= (K : Real>=0∞) ^ d * μH[d] (f '' s) := hf.hausdorffMeasure_preimage_le hd (f '' s)

Depends on / 依赖: hausdorffMeasure_preimage_le, hf.hausdorffMeasure_preimage_le, measure_mono, subset_preimage_image
-/
theorem le_hausdorffMeasure_image (hf : AntilipschitzWith K f) (hd : 0 <= d) (s : Set X) :
    μH[d] s <= (K : Real>=0∞) ^ d * μH[d] (f '' s) :=
  calc
    μH[d] s <= μH[d] (f ⁻¹' f '' s) := measure_mono (subset_preimage_image _ _)
    _ <= (K : Real>=0∞) ^ d * μH[d] (f '' s) := hf.hausdorffMeasure_preimage_le hd (f '' s)

end AntilipschitzWith

/-!
### Isometries preserve the Hausdorff measure and Hausdorff dimension
-/


namespace Isometry

variable {f : X -> Y} {d : Real}

/--
theorem `hausdorffMeasure_image` / 定理 `hausdorffMeasure_image`

English:
theorem hausdorffMeasure_image
  given: (hf : Isometry f) (hd : 0 <= d ∨ Surjective f) (s : Set X)
  proof: by
  simp only [hausdorffMeasure, ← OuterMeasure.coe_mkMetric, ← OuterMeasure.comap_apply]
  rw [OuterMeasure.isometry_comap_mkMetric _ hf (hd.imp_left _)]
  exact ENNReal.monotone_rpow_of_nonneg

中文:
定理 hausdorffMeasure_image
  条件: (hf : 等距 f) (hd : 0 <= d ∨ 满射 f) (s : 集合 X)
  证明: by
  simp only [hausdorffMeasure, ← OuterMeasure.coe_mkMetric, ← OuterMeasure.comap_apply]
  rw [OuterMeasure.isometry_comap_mkMetric _ hf (hd.imp_left _)]
  exact ENNReal.monotone_rpow_of_nonneg

Depends on / 依赖: ENNReal, ENNReal.monotone_rpow_of_nonneg, OuterMeasure, OuterMeasure.coe_mkMetric, OuterMeasure.comap_apply, OuterMeasure.isometry_comap_mkMetric, coe_mkMetric, comap_apply, hausdorffMeasure, hd.imp_left, imp_left, isometry_comap_mkMetric, monotone_rpow_of_nonneg
-/
theorem hausdorffMeasure_image (hf : Isometry f) (hd : 0 <= d ∨ Surjective f) (s : Set X) :
    μH[d] (f '' s) = μH[d] s := by
  simp only [hausdorffMeasure, ← OuterMeasure.coe_mkMetric, ← OuterMeasure.comap_apply]
  rw [OuterMeasure.isometry_comap_mkMetric _ hf (hd.imp_left _)]
  exact ENNReal.monotone_rpow_of_nonneg

/--
theorem `hausdorffMeasure_preimage` / 定理 `hausdorffMeasure_preimage`

English:
theorem hausdorffMeasure_preimage
  given: (hf : Isometry f) (hd : 0 <= d ∨ Surjective f) (s : Set Y)
  proof: by
  rw [← hf.hausdorffMeasure_image hd]; rw [image_preimage_eq_inter_range]

中文:
定理 hausdorffMeasure_preimage
  条件: (hf : 等距 f) (hd : 0 <= d ∨ 满射 f) (s : 集合 Y)
  证明: by
  rw [← hf.hausdorffMeasure_image hd]; rw [image_preimage_eq_inter_range]

Depends on / 依赖: hausdorffMeasure_image, hf.hausdorffMeasure_image, image_preimage_eq_inter_range
-/
theorem hausdorffMeasure_preimage (hf : Isometry f) (hd : 0 <= d ∨ Surjective f) (s : Set Y) :
    μH[d] (f ⁻¹' s) = μH[d] (s inter range f) := by
  rw [← hf.hausdorffMeasure_image hd]; rw [image_preimage_eq_inter_range]

/--
theorem `map_hausdorffMeasure` / 定理 `map_hausdorffMeasure`

English:
theorem map_hausdorffMeasure
  given: (hf : Isometry f) (hd : 0 <= d ∨ Surjective f)
  proof: by
  ext1 s hs
  rw [map_apply hf.continuous.measurable hs]; rw [Measure.restrict_apply hs]; rw [hf.hausdorffMeasure_preimage hd]

中文:
定理 map_hausdorffMeasure
  条件: (hf : 等距 f) (hd : 0 <= d ∨ 满射 f)
  证明: by
  ext1 s hs
  rw [map_apply hf.continuous.measurable hs]; rw [Measure.restrict_apply hs]; rw [hf.hausdorffMeasure_preimage hd]

Depends on / 依赖: Measure, Measure.restrict_apply, continuous, hausdorffMeasure_preimage, hf.continuous.measurable, hf.hausdorffMeasure_preimage, map_apply, measurable, restrict_apply
-/
theorem map_hausdorffMeasure (hf : Isometry f) (hd : 0 <= d ∨ Surjective f) :
    Measure.map f μH[d] = μH[d].restrict (range f) := by
  ext1 s hs
  rw [map_apply hf.continuous.measurable hs]; rw [Measure.restrict_apply hs]; rw [hf.hausdorffMeasure_preimage hd]

end Isometry

namespace IsometryEquiv

@[simp]
/--
theorem `hausdorffMeasure_image` / 定理 `hausdorffMeasure_image`

English:
theorem hausdorffMeasure_image
  given: (e : X ≃ᵢ Y) (d : Real) (s : Set X)
  statement: μH[d] (e '' s) = μH[d] s
  proof: e.isometry.hausdorffMeasure_image (Or.inr e.surjective) s

@[simp]

中文:
定理 hausdorffMeasure_image
  条件: (e : X ≃ᵢ Y) (d : 实数) (s : 集合 X)
  结论: μH[d] (e '' s) = μH[d] s
  证明: e.isometry.hausdorffMeasure_image (Or.inr e.surjective) s

@[simp]

Depends on / 依赖: Or.inr, e.isometry.hausdorffMeasure_image, e.surjective, hausdorffMeasure_image, isometry, surjective
-/
theorem hausdorffMeasure_image (e : X ≃ᵢ Y) (d : Real) (s : Set X) : μH[d] (e '' s) = μH[d] s :=
  e.isometry.hausdorffMeasure_image (Or.inr e.surjective) s

@[simp]
/--
theorem `hausdorffMeasure_preimage` / 定理 `hausdorffMeasure_preimage`

English:
theorem hausdorffMeasure_preimage
  given: (e : X ≃ᵢ Y) (d : Real) (s : Set Y)
  statement: μH[d] (e ⁻¹' s) = μH[d] s
  proof: by
  rw [← e.image_symm]; rw [e.symm.hausdorffMeasure_image]

@[simp]

中文:
定理 hausdorffMeasure_preimage
  条件: (e : X ≃ᵢ Y) (d : 实数) (s : 集合 Y)
  结论: μH[d] (e ⁻¹' s) = μH[d] s
  证明: by
  rw [← e.image_symm]; rw [e.symm.hausdorffMeasure_image]

@[simp]

Depends on / 依赖: e.image_symm, e.symm.hausdorffMeasure_image, hausdorffMeasure_image, image_symm
-/
theorem hausdorffMeasure_preimage (e : X ≃ᵢ Y) (d : Real) (s : Set Y) : μH[d] (e ⁻¹' s) = μH[d] s := by
  rw [← e.image_symm]; rw [e.symm.hausdorffMeasure_image]

@[simp]
/--
theorem `map_hausdorffMeasure` / 定理 `map_hausdorffMeasure`

English:
theorem map_hausdorffMeasure
  given: (e : X ≃ᵢ Y) (d : Real)
  statement: Measure.map e μH[d] = μH[d]
  proof: by
  rw [e.isometry.map_hausdorffMeasure (Or.inr e.surjective)]; rw [e.surjective.range_eq]; rw [restrict_univ]

中文:
定理 map_hausdorffMeasure
  条件: (e : X ≃ᵢ Y) (d : 实数)
  结论: 测度.map e μH[d] = μH[d]
  证明: by
  rw [e.isometry.map_hausdorffMeasure (Or.inr e.surjective)]; rw [e.surjective.range_eq]; rw [restrict_univ]

Depends on / 依赖: Or.inr, e.isometry.map_hausdorffMeasure, e.surjective, e.surjective.range_eq, isometry, map_hausdorffMeasure, range_eq, restrict_univ, surjective
-/
theorem map_hausdorffMeasure (e : X ≃ᵢ Y) (d : Real) : Measure.map e μH[d] = μH[d] := by
  rw [e.isometry.map_hausdorffMeasure (Or.inr e.surjective)]; rw [e.surjective.range_eq]; rw [restrict_univ]

/--
theorem `measurePreserving_hausdorffMeasure` / 定理 `measurePreserving_hausdorffMeasure`

English:
theorem measurePreserving_hausdorffMeasure
  given: (e : X ≃ᵢ Y) (d : Real)
  statement: MeasurePreserving e μH[d] μH[d]
  proof: ⟨e.continuous.measurable, map_hausdorffMeasure _ _⟩

中文:
定理 measurePreserving_hausdorffMeasure
  条件: (e : X ≃ᵢ Y) (d : 实数)
  结论: 保测 e μH[d] μH[d]
  证明: ⟨e.continuous.measurable, map_hausdorffMeasure _ _⟩

Depends on / 依赖: continuous, e.continuous.measurable, map_hausdorffMeasure, measurable
-/
theorem measurePreserving_hausdorffMeasure (e : X ≃ᵢ Y) (d : Real) : MeasurePreserving e μH[d] μH[d] :=
  ⟨e.continuous.measurable, map_hausdorffMeasure _ _⟩

end IsometryEquiv

namespace MeasureTheory

@[to_additive]
/--
theorem `hausdorffMeasure_smul` / 定理 `hausdorffMeasure_smul`

English:
theorem hausdorffMeasure_smul
  statement: {α : Type*} [SMul α X] [IsIsometricSMul α X] {d : Real} (c : α)
  proof: (isometry_smul X c).hausdorffMeasure_image h _

@[to_additive]

中文:
定理 hausdorffMeasure_smul
  结论: {α : 类型} [标量乘法 α X] [是是ometricSMul α X] {d : 实数} (c : α)
  证明: (isometry_smul X c).hausdorffMeasure_image h _

@[to_additive]

Depends on / 依赖: hausdorffMeasure_image, isometry_smul
-/
theorem hausdorffMeasure_smul {α : Type*} [SMul α X] [IsIsometricSMul α X] {d : Real} (c : α)
    (h : 0 <= d ∨ Surjective (c • · : X -> X)) (s : Set X) : μH[d] (c • s) = μH[d] s :=
  (isometry_smul X c).hausdorffMeasure_image h _

@[to_additive]
instance {α : Type*} [Group α] [MulAction α X] [IsIsometricSMul α X] {d : Real} :
    SMulInvariantMeasure α X μH[d] where
  measure_preimage_smul c _ _ := (IsometryEquiv.constSMul c).hausdorffMeasure_preimage _ _

@[to_additive]
instance {d : Real} [Group X] [IsIsometricSMul X X] : IsMulLeftInvariant (μH[d] : Measure X) where
  map_mul_left_eq_self x := (IsometryEquiv.constSMul x).map_hausdorffMeasure _

@[to_additive]
instance {d : Real} [Group X] [IsIsometricSMul Xᵐᵒᵖ X] : IsMulRightInvariant (μH[d] : Measure X) where
  map_mul_right_eq_self x := (IsometryEquiv.constSMul (MulOpposite.op x)).map_hausdorffMeasure _

/-!
### Hausdorff measure and Lebesgue measure
-/


/-- In the space `ι → ℝ`, the Hausdorff measure coincides exactly with the Lebesgue measure. -/
@[simp]
/--
theorem `hausdorffMeasure_pi_real` / 定理 `hausdorffMeasure_pi_real`

English:
theorem hausdorffMeasure_pi_real
  given: {ι : Type*} [Fintype ι]
  proof: by
  classical
  -- it suffices to check that the two measures coincide on products of rational intervals
  refine (pi_eq_generateFrom (fun _ => Real.borel_eq_generateFrom_Ioo_rat.symm)
    (fun _ => Real.isPiSystem_Ioo_rat) (fun _ => Real.finiteSpanningSetsInIooRat _) ?_).symm
  simp only [mem_iUnion, mem_singleton_iff]
  -- fix such a product `s` of rational intervals, of the form `Π (a i, b i)`.
  intro s hs
  choose a b H using hs
  obtain rfl : s = fun i => Ioo (α := Real) (a i) (b i) := funext fun i => (H i).2
  replace H := fun i => (H i).1
  apply le_antisymm _
  -- first check that `volume s ≤ μH s`
  · have Hle : volume <= (μH[Fintype.card ι] : Measure (ι -> Real)) := by
      refine le_hausdorffMeasure _ _ ∞ ENNReal.coe_lt_top fun s _ => ?_
      rw [ENNReal.rpow_natCast]
      exact Real.volume_pi_le_diam_pow s
    rw [← volume_pi_pi fun i => Ioo (a i : Real) (b i)]
    exact Measure.le_iff'.1 Hle _
  /- For the other inequality `μH s ≤ volume s`, we use a covering of `s` by sets of small diameter
    `1/n`, namely cubes with left-most point of the form `a i + f i / n` with `f i` ranging between
    `0` and `⌈(b i - a i) * n⌉`. Their number is asymptotic to `n^d * Π (b i - a i)`. -/
  have I : forall i, 0 <= (b i : Real) - a i := fun i => by
    simpa only [sub_nonneg, Rat.cast_le] using (H i).le
  let γ := fun n : Nat => forall i : ι, Fin ⌈((b i : Real) - a i) * n⌉₊
  let t : forall n : Nat, γ n -> Set (ι -> Real) := fun n f =>
    Set.pi univ fun i => Icc (a i + f i / n) (a i + (f i + 1) / n)
  have A : Tendsto (fun n : Nat => 1 / (n : Real>=0∞)) atTop (𝓝 0) := by
    simp only [one_div, ENNReal.tendsto_inv_nat_nhds_zero]
  have B : forallᶠ n in atTop, forall i : γ n, ediam (t n i) <= 1 / n := by
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    intro f
    refine ediam_pi_le_of_le fun b => ?_
    simp only [Real.ediam_Icc, add_div, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hn), le_refl,
      add_sub_add_left_eq_sub, add_sub_cancel_left, ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  have C : forallᶠ n in atTop, (Set.pi univ fun i : ι => Ioo (a i : Real) (b i)) subseteq ⋃ i : γ n, t n i := by
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have npos : (0 : Real) < n := Nat.cast_pos.2 hn
    intro x hx
    simp only [mem_Ioo, mem_univ_pi] at hx
    simp only [t, mem_iUnion, mem_univ_pi]
    let f : γ n := fun i =>
      ⟨⌊(x i - a i) * n⌋₊, by
        apply Nat.floor_lt_ceil_of_lt_of_pos
        · gcongr
          exact (hx i).right
        · refine mul_pos ?_ npos
          simpa only [Rat.cast_lt, sub_pos] using H i⟩
    refine ⟨f, fun i => ⟨?_, ?_⟩⟩
    · calc
        (a i : Real) + ⌊(x i - a i) * n⌋₊ / n <= (a i : Real) + (x i - a i) * n / n := by
          gcongr
          exact Nat.floor_le (mul_nonneg (sub_nonneg.2 (hx i).1.le) npos.le)
        _ = x i := by field
    · calc
        x i = (a i : Real) + (x i - a i) * n / n := by field
        _ <= (a i : Real) + (⌊(x i - a i) * n⌋₊ + 1) / n := by
          gcongr
          exact (Nat.lt_floor_add_one _).le
  calc
    μH[Fintype.card ι] (Set.pi univ fun i : ι => Ioo (a i : Real) (b i)) <=
        liminf (fun n : Nat => ∑ i : γ n, ediam (t n i) ^ ((Fintype.card ι) : Real)) atTop :=
      hausdorffMeasure_le_liminf_sum _ (Set.pi univ fun i => Ioo (a i : Real) (b i))
        (fun n : Nat => 1 / (n : Real>=0∞)) A t B C
    _ <= liminf (fun n : Nat => ∑ i : γ n, (1 / (n : Real>=0∞)) ^ Fintype.card ι) atTop := by
      refine liminf_le_liminf ?_ ?_
      · filter_upwards [B] with _ hn
        apply Finset.sum_le_sum fun i _ => _
        simp only [ENNReal.rpow_natCast]
        intro i _
        exact pow_le_pow_left' (hn i) _
      · isBoundedDefault
    _ = liminf (fun n : Nat => ∏ i : ι, (⌈((b i : Real) - a i) * n⌉₊ : Real>=0∞) / n) atTop := by
      simp only [γ, Finset.card_univ, Nat.cast_prod, one_mul, Fintype.card_fin, Finset.sum_const,
        nsmul_eq_mul, Fintype.card_pi, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const]
    _ = ∏ i : ι, volume (Ioo (a i : Real) (b i)) := by
      simp only [Real.volume_Ioo]
      apply Tendsto.liminf_eq
      refine ENNReal.tendsto_finsetProd_of_ne_top _ (fun i _ => ?_) fun i _ => ?_
      · apply
          Tendsto.congr' _
            ((ENNReal.continuous_ofReal.tendsto _).comp
              ((tendsto_nat_ceil_mul_div_atTop (I i)).comp tendsto_natCast_atTop_atTop))
        apply eventually_atTop.2 ⟨1, fun n hn => _⟩
        intro n hn
        simp only [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hn), comp_apply,
          ENNReal.ofReal_natCast]
      · simp only [ENNReal.ofReal_ne_top, Ne, not_false_iff]

中文:
定理 hausdorffMeasure_pi_real
  条件: {ι : 类型} [有限类型 ι]
  证明: by
  classical
  -- it suffices to check that the two measures coincide on products of rational intervals
  refine (pi_eq_generateFrom (fun _ => Real.borel_eq_generateFrom_Ioo_rat.symm)
    (fun _ => Real.isPiSystem_Ioo_rat) (fun _ => Real.finiteSpanningSetsInIooRat _) ?_).symm
  simp only [mem_iUnion, mem_singleton_iff]
  -- fix such a product `s` of rational intervals, of the form `Π (a i, b i)`.
  intro s hs
  choose a b H using hs
  obtain rfl : s = fun i => Ioo (α := Real) (a i) (b i) := funext fun i => (H i).2
  replace H := fun i => (H i).1
  apply le_antisymm _
  -- first check that `volume s ≤ μH s`
  · have Hle : volume <= (μH[Fintype.card ι] : Measure (ι -> Real)) := by
      refine le_hausdorffMeasure _ _ ∞ ENNReal.coe_lt_top fun s _ => ?_
      rw [ENNReal.rpow_natCast]
      exact Real.volume_pi_le_diam_pow s
    rw [← volume_pi_pi fun i => Ioo (a i : Real) (b i)]
    exact Measure.le_iff'.1 Hle _
  /- For the other inequality `μH s ≤ volume s`, we use a covering of `s` by sets of small diameter
    `1/n`, namely cubes with left-most point of the form `a i + f i / n` with `f i` ranging between
    `0` and `⌈(b i - a i) * n⌉`. Their number is asymptotic to `n^d * Π (b i - a i)`. -/
  have I : forall i, 0 <= (b i : Real) - a i := fun i => by
    simpa only [sub_nonneg, Rat.cast_le] using (H i).le
  let γ := fun n : Nat => forall i : ι, Fin ⌈((b i : Real) - a i) * n⌉₊
  let t : forall n : Nat, γ n -> Set (ι -> Real) := fun n f =>
    Set.pi univ fun i => Icc (a i + f i / n) (a i + (f i + 1) / n)
  have A : Tendsto (fun n : Nat => 1 / (n : Real>=0∞)) atTop (𝓝 0) := by
    simp only [one_div, ENNReal.tendsto_inv_nat_nhds_zero]
  have B : forallᶠ n in atTop, forall i : γ n, ediam (t n i) <= 1 / n := by
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    intro f
    refine ediam_pi_le_of_le fun b => ?_
    simp only [Real.ediam_Icc, add_div, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hn), le_refl,
      add_sub_add_left_eq_sub, add_sub_cancel_left, ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  have C : forallᶠ n in atTop, (Set.pi univ fun i : ι => Ioo (a i : Real) (b i)) subseteq ⋃ i : γ n, t n i := by
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have npos : (0 : Real) < n := Nat.cast_pos.2 hn
    intro x hx
    simp only [mem_Ioo, mem_univ_pi] at hx
    simp only [t, mem_iUnion, mem_univ_pi]
    let f : γ n := fun i =>
      ⟨⌊(x i - a i) * n⌋₊, by
        apply Nat.floor_lt_ceil_of_lt_of_pos
        · gcongr
          exact (hx i).right
        · refine mul_pos ?_ npos
          simpa only [Rat.cast_lt, sub_pos] using H i⟩
    refine ⟨f, fun i => ⟨?_, ?_⟩⟩
    · calc
        (a i : Real) + ⌊(x i - a i) * n⌋₊ / n <= (a i : Real) + (x i - a i) * n / n := by
          gcongr
          exact Nat.floor_le (mul_nonneg (sub_nonneg.2 (hx i).1.le) npos.le)
        _ = x i := by field
    · calc
        x i = (a i : Real) + (x i - a i) * n / n := by field
        _ <= (a i : Real) + (⌊(x i - a i) * n⌋₊ + 1) / n := by
          gcongr
          exact (Nat.lt_floor_add_one _).le
  calc
    μH[Fintype.card ι] (Set.pi univ fun i : ι => Ioo (a i : Real) (b i)) <=
        liminf (fun n : Nat => ∑ i : γ n, ediam (t n i) ^ ((Fintype.card ι) : Real)) atTop :=
      hausdorffMeasure_le_liminf_sum _ (Set.pi univ fun i => Ioo (a i : Real) (b i))
        (fun n : Nat => 1 / (n : Real>=0∞)) A t B C
    _ <= liminf (fun n : Nat => ∑ i : γ n, (1 / (n : Real>=0∞)) ^ Fintype.card ι) atTop := by
      refine liminf_le_liminf ?_ ?_
      · filter_upwards [B] with _ hn
        apply Finset.sum_le_sum fun i _ => _
        simp only [ENNReal.rpow_natCast]
        intro i _
        exact pow_le_pow_left' (hn i) _
      · isBoundedDefault
    _ = liminf (fun n : Nat => ∏ i : ι, (⌈((b i : Real) - a i) * n⌉₊ : Real>=0∞) / n) atTop := by
      simp only [γ, Finset.card_univ, Nat.cast_prod, one_mul, Fintype.card_fin, Finset.sum_const,
        nsmul_eq_mul, Fintype.card_pi, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const]
    _ = ∏ i : ι, volume (Ioo (a i : Real) (b i)) := by
      simp only [Real.volume_Ioo]
      apply Tendsto.liminf_eq
      refine ENNReal.tendsto_finsetProd_of_ne_top _ (fun i _ => ?_) fun i _ => ?_
      · apply
          Tendsto.congr' _
            ((ENNReal.continuous_ofReal.tendsto _).comp
              ((tendsto_nat_ceil_mul_div_atTop (I i)).comp tendsto_natCast_atTop_atTop))
        apply eventually_atTop.2 ⟨1, fun n hn => _⟩
        intro n hn
        simp only [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hn), comp_apply,
          ENNReal.ofReal_natCast]
      · simp only [ENNReal.ofReal_ne_top, Ne, not_false_iff]

Depends on / 依赖: classical
-/
theorem hausdorffMeasure_pi_real {ι : Type*} [Fintype ι] :
    (μH[Fintype.card ι] : Measure (ι -> Real)) = volume := by
  classical
  -- it suffices to check that the two measures coincide on products of rational intervals
  refine (pi_eq_generateFrom (fun _ => Real.borel_eq_generateFrom_Ioo_rat.symm)
    (fun _ => Real.isPiSystem_Ioo_rat) (fun _ => Real.finiteSpanningSetsInIooRat _) ?_).symm
  simp only [mem_iUnion, mem_singleton_iff]
  -- fix such a product `s` of rational intervals, of the form `Π (a i, b i)`.
  intro s hs
  choose a b H using hs
  obtain rfl : s = fun i => Ioo (α := Real) (a i) (b i) := funext fun i => (H i).2
  replace H := fun i => (H i).1
  apply le_antisymm _
  -- first check that `volume s ≤ μH s`
  · have Hle : volume <= (μH[Fintype.card ι] : Measure (ι -> Real)) := by
      refine le_hausdorffMeasure _ _ ∞ ENNReal.coe_lt_top fun s _ => ?_
      rw [ENNReal.rpow_natCast]
      exact Real.volume_pi_le_diam_pow s
    rw [← volume_pi_pi fun i => Ioo (a i : Real) (b i)]
    exact Measure.le_iff'.1 Hle _
  /- For the other inequality `μH s ≤ volume s`, we use a covering of `s` by sets of small diameter
    `1/n`, namely cubes with left-most point of the form `a i + f i / n` with `f i` ranging between
    `0` and `⌈(b i - a i) * n⌉`. Their number is asymptotic to `n^d * Π (b i - a i)`. -/
  have I : forall i, 0 <= (b i : Real) - a i := fun i => by
    simpa only [sub_nonneg, Rat.cast_le] using (H i).le
  let γ := fun n : Nat => forall i : ι, Fin ⌈((b i : Real) - a i) * n⌉₊
  let t : forall n : Nat, γ n -> Set (ι -> Real) := fun n f =>
    Set.pi univ fun i => Icc (a i + f i / n) (a i + (f i + 1) / n)
  have A : Tendsto (fun n : Nat => 1 / (n : Real>=0∞)) atTop (𝓝 0) := by
    simp only [one_div, ENNReal.tendsto_inv_nat_nhds_zero]
  have B : forallᶠ n in atTop, forall i : γ n, ediam (t n i) <= 1 / n := by
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    intro f
    refine ediam_pi_le_of_le fun b => ?_
    simp only [Real.ediam_Icc, add_div, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hn), le_refl,
      add_sub_add_left_eq_sub, add_sub_cancel_left, ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  have C : forallᶠ n in atTop, (Set.pi univ fun i : ι => Ioo (a i : Real) (b i)) subseteq ⋃ i : γ n, t n i := by
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    have npos : (0 : Real) < n := Nat.cast_pos.2 hn
    intro x hx
    simp only [mem_Ioo, mem_univ_pi] at hx
    simp only [t, mem_iUnion, mem_univ_pi]
    let f : γ n := fun i =>
      ⟨⌊(x i - a i) * n⌋₊, by
        apply Nat.floor_lt_ceil_of_lt_of_pos
        · gcongr
          exact (hx i).right
        · refine mul_pos ?_ npos
          simpa only [Rat.cast_lt, sub_pos] using H i⟩
    refine ⟨f, fun i => ⟨?_, ?_⟩⟩
    · calc
        (a i : Real) + ⌊(x i - a i) * n⌋₊ / n <= (a i : Real) + (x i - a i) * n / n := by
          gcongr
          exact Nat.floor_le (mul_nonneg (sub_nonneg.2 (hx i).1.le) npos.le)
        _ = x i := by field
    · calc
        x i = (a i : Real) + (x i - a i) * n / n := by field
        _ <= (a i : Real) + (⌊(x i - a i) * n⌋₊ + 1) / n := by
          gcongr
          exact (Nat.lt_floor_add_one _).le
  calc
    μH[Fintype.card ι] (Set.pi univ fun i : ι => Ioo (a i : Real) (b i)) <=
        liminf (fun n : Nat => ∑ i : γ n, ediam (t n i) ^ ((Fintype.card ι) : Real)) atTop :=
      hausdorffMeasure_le_liminf_sum _ (Set.pi univ fun i => Ioo (a i : Real) (b i))
        (fun n : Nat => 1 / (n : Real>=0∞)) A t B C
    _ <= liminf (fun n : Nat => ∑ i : γ n, (1 / (n : Real>=0∞)) ^ Fintype.card ι) atTop := by
      refine liminf_le_liminf ?_ ?_
      · filter_upwards [B] with _ hn
        apply Finset.sum_le_sum fun i _ => _
        simp only [ENNReal.rpow_natCast]
        intro i _
        exact pow_le_pow_left' (hn i) _
      · isBoundedDefault
    _ = liminf (fun n : Nat => ∏ i : ι, (⌈((b i : Real) - a i) * n⌉₊ : Real>=0∞) / n) atTop := by
      simp only [γ, Finset.card_univ, Nat.cast_prod, one_mul, Fintype.card_fin, Finset.sum_const,
        nsmul_eq_mul, Fintype.card_pi, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const]
    _ = ∏ i : ι, volume (Ioo (a i : Real) (b i)) := by
      simp only [Real.volume_Ioo]
      apply Tendsto.liminf_eq
      refine ENNReal.tendsto_finsetProd_of_ne_top _ (fun i _ => ?_) fun i _ => ?_
      · apply
          Tendsto.congr' _
            ((ENNReal.continuous_ofReal.tendsto _).comp
              ((tendsto_nat_ceil_mul_div_atTop (I i)).comp tendsto_natCast_atTop_atTop))
        apply eventually_atTop.2 ⟨1, fun n hn => _⟩
        intro n hn
        simp only [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr hn), comp_apply,
          ENNReal.ofReal_natCast]
      · simp only [ENNReal.ofReal_ne_top, Ne, not_false_iff]

/--
Instance `isAddHaarMeasure_hausdorffMeasure` / 实例 `isAddHaarMeasure_hausdorffMeasure`

English:
instance isAddHaarMeasure_hausdorffMeasure
  signature: {E : Type*}
  body: by
    set e : E ≃L[Real] Fin (finrank Real E) -> Real := ContinuousLinearEquiv.ofFinrankEq (by simp)
    suffices μH[finrank Real E] (e '' K) < ⊤ by
      rw [← e.symm_image_image K]
apply lt_of_le_of_lt e.symm.lipschitz.hausdorffMeasure_image_le (by simp) (e '' K)
      rw [ENNReal.rpow_natCast]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) this
    conv_lhs => congr; congr; rw [← Fintype.card_fin (finrank Real E)]
    rw [hausdorffMeasure_pi_real]
    exact (hK.image e.continuous).measure_lt_top
  open_pos U hU hU' := by
    set e : E ≃L[Real] Fin (finrank Real E) -> Real := ContinuousLinearEquiv.ofFinrankEq (by simp)
    suffices 0 < μH[finrank Real E] (e '' U) from
      (ENNReal.mul_pos_iff.mp (lt_of_lt_of_le this <|
        e.lipschitz.hausdorffMeasure_image_le (by simp) _)).2.ne'
    conv_rhs => congr; congr; rw [← Fintype.card_fin (finrank Real E)]
    rw [hausdorffMeasure_pi_real]
    apply (e.isOpenMap U hU).measure_pos (μ := volume)
    simpa

中文:
实例 isAddHaarMeasure_hausdorffMeasure
  签名: {E : 类型}
  定义体: by
    set e : E ≃L[Real] Fin (finrank Real E) -> Real := ContinuousLinearEquiv.ofFinrankEq (by simp)
    suffices μH[finrank Real E] (e '' K) < ⊤ by
      rw [← e.symm_image_image K]
apply lt_of_le_of_lt e.symm.lipschitz.hausdorffMeasure_image_le (by simp) (e '' K)
      rw [ENNReal.rpow_natCast]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) this
    conv_lhs => congr; congr; rw [← Fintype.card_fin (finrank Real E)]
    rw [hausdorffMeasure_pi_real]
    exact (hK.image e.continuous).measure_lt_top
  open_pos U hU hU' := by
    set e : E ≃L[Real] Fin (finrank Real E) -> Real := ContinuousLinearEquiv.ofFinrankEq (by simp)
    suffices 0 < μH[finrank Real E] (e '' U) from
      (ENNReal.mul_pos_iff.mp (lt_of_lt_of_le this <|
        e.lipschitz.hausdorffMeasure_image_le (by simp) _)).2.ne'
    conv_rhs => congr; congr; rw [← Fintype.card_fin (finrank Real E)]
    rw [hausdorffMeasure_pi_real]
    apply (e.isOpenMap U hU).measure_pos (μ := volume)
    simpa

Depends on / 依赖: finrank
-/
instance isAddHaarMeasure_hausdorffMeasure {E : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
    [MeasurableSpace E] [BorelSpace E] :
    IsAddHaarMeasure (G := E) μH[finrank Real E] where
  lt_top_of_isCompact K hK := by
    set e : E ≃L[Real] Fin (finrank Real E) -> Real := ContinuousLinearEquiv.ofFinrankEq (by simp)
    suffices μH[finrank Real E] (e '' K) < ⊤ by
      rw [← e.symm_image_image K]
apply lt_of_le_of_lt e.symm.lipschitz.hausdorffMeasure_image_le (by simp) (e '' K)
      rw [ENNReal.rpow_natCast]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) this
    conv_lhs => congr; congr; rw [← Fintype.card_fin (finrank Real E)]
    rw [hausdorffMeasure_pi_real]
    exact (hK.image e.continuous).measure_lt_top
  open_pos U hU hU' := by
    set e : E ≃L[Real] Fin (finrank Real E) -> Real := ContinuousLinearEquiv.ofFinrankEq (by simp)
    suffices 0 < μH[finrank Real E] (e '' U) from
      (ENNReal.mul_pos_iff.mp (lt_of_lt_of_le this <|
        e.lipschitz.hausdorffMeasure_image_le (by simp) _)).2.ne'
    conv_rhs => congr; congr; rw [← Fintype.card_fin (finrank Real E)]
    rw [hausdorffMeasure_pi_real]
    apply (e.isOpenMap U hU).measure_pos (μ := volume)
    simpa

variable (ι X)

/--
theorem `hausdorffMeasure_measurePreserving_funUnique` / 定理 `hausdorffMeasure_measurePreserving_funUnique`

English:
theorem hausdorffMeasure_measurePreserving_funUnique
  given: [Unique ι] (d : Real)
  proof: (IsometryEquiv.funUnique ι X).measurePreserving_hausdorffMeasure _

中文:
定理 hausdorffMeasure_measurePreserving_funUnique
  条件: [唯一 ι] (d : 实数)
  证明: (IsometryEquiv.funUnique ι X).measurePreserving_hausdorffMeasure _

Depends on / 依赖: IsometryEquiv, IsometryEquiv.funUnique, funUnique, measurePreserving_hausdorffMeasure
-/
theorem hausdorffMeasure_measurePreserving_funUnique [Unique ι] (d : Real) :
    MeasurePreserving (MeasurableEquiv.funUnique ι X) μH[d] μH[d] :=
  (IsometryEquiv.funUnique ι X).measurePreserving_hausdorffMeasure _

/--
theorem `hausdorffMeasure_measurePreserving_piFinTwo` / 定理 `hausdorffMeasure_measurePreserving_piFinTwo`

English:
theorem hausdorffMeasure_measurePreserving_piFinTwo
  statement: (α : Fin 2 -> Type*)
  proof: (IsometryEquiv.piFinTwo α).measurePreserving_hausdorffMeasure _

中文:
定理 hausdorffMeasure_measurePreserving_piFinTwo
  结论: (α : 有限集 2 -> 类型)
  证明: (IsometryEquiv.piFinTwo α).measurePreserving_hausdorffMeasure _

Depends on / 依赖: IsometryEquiv, IsometryEquiv.piFinTwo, measurePreserving_hausdorffMeasure, piFinTwo
-/
theorem hausdorffMeasure_measurePreserving_piFinTwo (α : Fin 2 -> Type*)
    [forall i, MeasurableSpace (α i)] [forall i, EMetricSpace (α i)] [forall i, BorelSpace (α i)]
    [forall i, SecondCountableTopology (α i)] (d : Real) :
    MeasurePreserving (MeasurableEquiv.piFinTwo α) μH[d] μH[d] :=
  (IsometryEquiv.piFinTwo α).measurePreserving_hausdorffMeasure _

/-- In the space `ℝ`, the Hausdorff measure coincides exactly with the Lebesgue measure. -/
@[simp]
/--
theorem `hausdorffMeasure_real` / 定理 `hausdorffMeasure_real`

English:
theorem hausdorffMeasure_real
  statement: (μH[1] : Measure Real) = volume
  proof: by
  rw [← (volume_preserving_funUnique Unit Real).map_eq]; rw [← (hausdorffMeasure_measurePreserving_funUnique Unit Real 1).map_eq]; rw [← hausdorffMeasure_pi_real]; rw [Fintype.card_unit]; rw [Nat.cast_one]

中文:
定理 hausdorffMeasure_real
  结论: (μH[1] : 测度 实数) = volume
  证明: by
  rw [← (volume_preserving_funUnique Unit Real).map_eq]; rw [← (hausdorffMeasure_measurePreserving_funUnique Unit Real 1).map_eq]; rw [← hausdorffMeasure_pi_real]; rw [Fintype.card_unit]; rw [Nat.cast_one]

Depends on / 依赖: Fintype, Fintype.card_unit, Nat.cast_one, card_unit, cast_one, hausdorffMeasure_measurePreserving_funUnique, hausdorffMeasure_pi_real, map_eq, volume_preserving_funUnique
-/
theorem hausdorffMeasure_real : (μH[1] : Measure Real) = volume := by
  rw [← (volume_preserving_funUnique Unit Real).map_eq]; rw [← (hausdorffMeasure_measurePreserving_funUnique Unit Real 1).map_eq]; rw [← hausdorffMeasure_pi_real]; rw [Fintype.card_unit]; rw [Nat.cast_one]

/-- In the space `ℝ × ℝ`, the Hausdorff measure coincides exactly with the Lebesgue measure. -/
@[simp]
/--
theorem `hausdorffMeasure_prod_real` / 定理 `hausdorffMeasure_prod_real`

English:
theorem hausdorffMeasure_prod_real
  statement: (μH[2] : Measure (Real × Real)) = volume
  proof: by
  rw [← (volume_preserving_piFinTwo fun _ => Real).map_eq]; rw [← (hausdorffMeasure_measurePreserving_piFinTwo (fun _ => Real) _).map_eq]; rw [← hausdorffMeasure_pi_real]; rw [Fintype.card_fin]; rw [Nat.cast_two]

中文:
定理 hausdorffMeasure_prod_real
  结论: (μH[2] : 测度 (实数 × 实数)) = volume
  证明: by
  rw [← (volume_preserving_piFinTwo fun _ => Real).map_eq]; rw [← (hausdorffMeasure_measurePreserving_piFinTwo (fun _ => Real) _).map_eq]; rw [← hausdorffMeasure_pi_real]; rw [Fintype.card_fin]; rw [Nat.cast_two]

Depends on / 依赖: Fintype, Fintype.card_fin, Nat.cast_two, card_fin, cast_two, hausdorffMeasure_measurePreserving_piFinTwo, hausdorffMeasure_pi_real, map_eq, volume_preserving_piFinTwo
-/
theorem hausdorffMeasure_prod_real : (μH[2] : Measure (Real × Real)) = volume := by
  rw [← (volume_preserving_piFinTwo fun _ => Real).map_eq]; rw [← (hausdorffMeasure_measurePreserving_piFinTwo (fun _ => Real) _).map_eq]; rw [← hausdorffMeasure_pi_real]; rw [Fintype.card_fin]; rw [Nat.cast_two]

/-! ### Geometric results in affine spaces -/

section Geometric

variable {𝕜 E P : Type*}

/--
theorem `hausdorffMeasure_smul_right_image` / 定理 `hausdorffMeasure_smul_right_image`

English:
theorem hausdorffMeasure_smul_right_image
  statement: [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  obtain rfl | hv := eq_or_ne v 0
  · have := nullSingletonClass_hausdorff E one_pos
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    simp [hs]
  have hn : ‖v‖ != 0 := norm_ne_zero_iff.mpr hv
  -- break lineMap into pieces
  suffices
      μH[1] ((‖v‖ • ·) '' LinearMap.toSpanSingleton Real E (‖v‖⁻¹ • v) '' s) = ‖v‖₊ • μH[1] s by
    simpa only [Set.image_image, smul_comm (norm _), inv_smul_smul₀ hn,
      LinearMap.toSpanSingleton_apply] using this
  have iso_smul : Isometry (LinearMap.toSpanSingleton Real E (‖v‖⁻¹ • v)) := by
    refine AddMonoidHomClass.isometry_of_norm _ fun x => (norm_smul _ _).trans ?_
    rw [norm_smul]; rw [norm_inv]; rw [norm_norm]; rw [inv_mul_cancel₀ hn]; rw [mul_one]; rw [LinearMap.id_apply]
  rw [Set.image_smul]; rw [Measure.hausdorffMeasure_smul₀ zero_le_one hn]; rw [nnnorm_norm]; rw [NNReal.rpow_one]; rw [iso_smul.hausdorffMeasure_image (Or.inl <| zero_le_one' Real)]

中文:
定理 hausdorffMeasure_smul_right_image
  结论: [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  obtain rfl | hv := eq_or_ne v 0
  · have := nullSingletonClass_hausdorff E one_pos
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    simp [hs]
  have hn : ‖v‖ != 0 := norm_ne_zero_iff.mpr hv
  -- break lineMap into pieces
  suffices
      μH[1] ((‖v‖ • ·) '' LinearMap.toSpanSingleton Real E (‖v‖⁻¹ • v) '' s) = ‖v‖₊ • μH[1] s by
    simpa only [Set.image_image, smul_comm (norm _), inv_smul_smul₀ hn,
      LinearMap.toSpanSingleton_apply] using this
  have iso_smul : Isometry (LinearMap.toSpanSingleton Real E (‖v‖⁻¹ • v)) := by
    refine AddMonoidHomClass.isometry_of_norm _ fun x => (norm_smul _ _).trans ?_
    rw [norm_smul]; rw [norm_inv]; rw [norm_norm]; rw [inv_mul_cancel₀ hn]; rw [mul_one]; rw [LinearMap.id_apply]
  rw [Set.image_smul]; rw [Measure.hausdorffMeasure_smul₀ zero_le_one hn]; rw [nnnorm_norm]; rw [NNReal.rpow_one]; rw [iso_smul.hausdorffMeasure_image (Or.inl <| zero_le_one' Real)]

Depends on / 依赖: eq_empty_or_nonempty, eq_or_ne, norm_ne_zero_iff, norm_ne_zero_iff.mpr, nullSingletonClass_hausdorff, one_pos, s.eq_empty_or_nonempty
-/
theorem hausdorffMeasure_smul_right_image [NormedAddCommGroup E] [NormedSpace Real E]
    [MeasurableSpace E] [BorelSpace E] (v : E) (s : Set Real) :
    μH[1] ((fun r => r • v) '' s) = ‖v‖₊ • μH[1] s := by
  obtain rfl | hv := eq_or_ne v 0
  · have := nullSingletonClass_hausdorff E one_pos
    obtain rfl | hs := s.eq_empty_or_nonempty
    · simp
    simp [hs]
  have hn : ‖v‖ != 0 := norm_ne_zero_iff.mpr hv
  -- break lineMap into pieces
  suffices
      μH[1] ((‖v‖ • ·) '' LinearMap.toSpanSingleton Real E (‖v‖⁻¹ • v) '' s) = ‖v‖₊ • μH[1] s by
    simpa only [Set.image_image, smul_comm (norm _), inv_smul_smul₀ hn,
      LinearMap.toSpanSingleton_apply] using this
  have iso_smul : Isometry (LinearMap.toSpanSingleton Real E (‖v‖⁻¹ • v)) := by
    refine AddMonoidHomClass.isometry_of_norm _ fun x => (norm_smul _ _).trans ?_
    rw [norm_smul]; rw [norm_inv]; rw [norm_norm]; rw [inv_mul_cancel₀ hn]; rw [mul_one]; rw [LinearMap.id_apply]
  rw [Set.image_smul]; rw [Measure.hausdorffMeasure_smul₀ zero_le_one hn]; rw [nnnorm_norm]; rw [NNReal.rpow_one]; rw [iso_smul.hausdorffMeasure_image (Or.inl <| zero_le_one' Real)]

section NormedFieldAffine

variable [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [MeasurableSpace P]
variable [MetricSpace P] [NormedAddTorsor E P] [BorelSpace P]

/--
theorem `hausdorffMeasure_homothety_image` / 定理 `hausdorffMeasure_homothety_image`

English:
theorem hausdorffMeasure_homothety_image
  statement: {d : Real} (hd : 0 <= d) (x : P) {c : 𝕜} (hc : c != 0)
  proof: by
  suffices
    μH[d] (IsometryEquiv.vaddConst x '' (c • ·) '' (IsometryEquiv.vaddConst x).symm '' s) =
      ‖c‖₊ ^ d • μH[d] s by
    simpa only [Set.image_image]
  borelize E
  rw [IsometryEquiv.hausdorffMeasure_image]; rw [Set.image_smul]; rw [Measure.hausdorffMeasure_smul₀ hd hc]; rw [IsometryEquiv.hausdorffMeasure_image]

中文:
定理 hausdorffMeasure_homothety_image
  结论: {d : 实数} (hd : 0 <= d) (x : P) {c : 𝕜} (hc : c != 0)
  证明: by
  suffices
    μH[d] (IsometryEquiv.vaddConst x '' (c • ·) '' (IsometryEquiv.vaddConst x).symm '' s) =
      ‖c‖₊ ^ d • μH[d] s by
    simpa only [Set.image_image]
  borelize E
  rw [IsometryEquiv.hausdorffMeasure_image]; rw [Set.image_smul]; rw [Measure.hausdorffMeasure_smul₀ hd hc]; rw [IsometryEquiv.hausdorffMeasure_image]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.hausdorffMeasure_image, IsometryEquiv.vaddConst, Measure, Measure.hausdorffMeasure_smul, Set.image_image, Set.image_smul, borelize, hausdorffMeasure_image, image_image, image_smul, vaddConst
-/
theorem hausdorffMeasure_homothety_image {d : Real} (hd : 0 <= d) (x : P) {c : 𝕜} (hc : c != 0)
    (s : Set P) : μH[d] (AffineMap.homothety x c '' s) = ‖c‖₊ ^ d • μH[d] s := by
  suffices
    μH[d] (IsometryEquiv.vaddConst x '' (c • ·) '' (IsometryEquiv.vaddConst x).symm '' s) =
      ‖c‖₊ ^ d • μH[d] s by
    simpa only [Set.image_image]
  borelize E
  rw [IsometryEquiv.hausdorffMeasure_image]; rw [Set.image_smul]; rw [Measure.hausdorffMeasure_smul₀ hd hc]; rw [IsometryEquiv.hausdorffMeasure_image]

/--
theorem `hausdorffMeasure_homothety_preimage` / 定理 `hausdorffMeasure_homothety_preimage`

English:
theorem hausdorffMeasure_homothety_preimage
  statement: {d : Real} (hd : 0 <= d) (x : P) {c : 𝕜} (hc : c != 0)
  proof: by
  change μH[d] (AffineEquiv.homothetyUnitsMulHom x (Units.mk0 c hc) ⁻¹' s) = _
  rw [← AffineEquiv.image_symm]; rw [AffineEquiv.coe_homothetyUnitsMulHom_apply_symm]; rw [hausdorffMeasure_homothety_image hd x (_ : 𝕜ˣ).isUnit.ne_zero]; rw [Units.val_inv_eq_inv_val]; rw [Units.val_mk0]; rw [nnnorm_inv]

中文:
定理 hausdorffMeasure_homothety_preimage
  结论: {d : 实数} (hd : 0 <= d) (x : P) {c : 𝕜} (hc : c != 0)
  证明: by
  change μH[d] (AffineEquiv.homothetyUnitsMulHom x (Units.mk0 c hc) ⁻¹' s) = _
  rw [← AffineEquiv.image_symm]; rw [AffineEquiv.coe_homothetyUnitsMulHom_apply_symm]; rw [hausdorffMeasure_homothety_image hd x (_ : 𝕜ˣ).isUnit.ne_zero]; rw [Units.val_inv_eq_inv_val]; rw [Units.val_mk0]; rw [nnnorm_inv]

Depends on / 依赖: AffineEquiv, AffineEquiv.coe_homothetyUnitsMulHom_apply_symm, AffineEquiv.homothetyUnitsMulHom, AffineEquiv.image_symm, Units.mk0, Units.val_inv_eq_inv_val, Units.val_mk0, coe_homothetyUnitsMulHom_apply_symm, hausdorffMeasure_homothety_image, homothetyUnitsMulHom, image_symm, isUnit, isUnit.ne_zero, ne_zero, nnnorm_inv, val_inv_eq_inv_val, val_mk0
-/
theorem hausdorffMeasure_homothety_preimage {d : Real} (hd : 0 <= d) (x : P) {c : 𝕜} (hc : c != 0)
    (s : Set P) : μH[d] (AffineMap.homothety x c ⁻¹' s) = ‖c‖₊⁻¹ ^ d • μH[d] s := by
  change μH[d] (AffineEquiv.homothetyUnitsMulHom x (Units.mk0 c hc) ⁻¹' s) = _
  rw [← AffineEquiv.image_symm]; rw [AffineEquiv.coe_homothetyUnitsMulHom_apply_symm]; rw [hausdorffMeasure_homothety_image hd x (_ : 𝕜ˣ).isUnit.ne_zero]; rw [Units.val_inv_eq_inv_val]; rw [Units.val_mk0]; rw [nnnorm_inv]

/--
theorem `map_homothety_hausdorffMeasure` / 定理 `map_homothety_hausdorffMeasure`

English:
theorem map_homothety_hausdorffMeasure
  given: {d : Real} (hd : 0 <= d) (x : P) {c : 𝕜} (hc : c != 0)
  proof: by
  ext s hs
  rw [Measure.map_apply (AffineMap.homothety_continuous x c).measurable hs]; rw [hausdorffMeasure_homothety_preimage hd x hc s]; rw [Measure.smul_apply]

中文:
定理 map_homothety_hausdorffMeasure
  条件: {d : 实数} (hd : 0 <= d) (x : P) {c : 𝕜} (hc : c != 0)
  证明: by
  ext s hs
  rw [Measure.map_apply (AffineMap.homothety_continuous x c).measurable hs]; rw [hausdorffMeasure_homothety_preimage hd x hc s]; rw [Measure.smul_apply]

Depends on / 依赖: AffineMap, AffineMap.homothety_continuous, Measure, Measure.map_apply, Measure.smul_apply, hausdorffMeasure_homothety_preimage, homothety_continuous, map_apply, measurable, smul_apply
-/
theorem map_homothety_hausdorffMeasure {d : Real} (hd : 0 <= d) (x : P) {c : 𝕜} (hc : c != 0) :
    Measure.map (AffineMap.homothety x c) μH[d] = ‖c‖₊⁻¹ ^ d • μH[d] := by
  ext s hs
  rw [Measure.map_apply (AffineMap.homothety_continuous x c).measurable hs]; rw [hausdorffMeasure_homothety_preimage hd x hc s]; rw [Measure.smul_apply]

end NormedFieldAffine

section RealAffine

variable [NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace P]
variable [MetricSpace P] [NormedAddTorsor E P] [BorelSpace P]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `hausdorffMeasure_lineMap_image` / 定理 `hausdorffMeasure_lineMap_image`

English:
theorem hausdorffMeasure_lineMap_image
  given: (x y : P) (s : Set Real)
  proof: by
  suffices μH[1] (IsometryEquiv.vaddConst x '' (· • (y -ᵥ x)) '' s) = nndist x y • μH[1] s by
    simpa only [Set.image_image]
  borelize E
  rw [IsometryEquiv.hausdorffMeasure_image]; rw [hausdorffMeasure_smul_right_image]; rw [nndist_eq_nnnorm_vsub' E]

中文:
定理 hausdorffMeasure_lineMap_image
  条件: (x y : P) (s : 集合 实数)
  证明: by
  suffices μH[1] (IsometryEquiv.vaddConst x '' (· • (y -ᵥ x)) '' s) = nndist x y • μH[1] s by
    simpa only [Set.image_image]
  borelize E
  rw [IsometryEquiv.hausdorffMeasure_image]; rw [hausdorffMeasure_smul_right_image]; rw [nndist_eq_nnnorm_vsub' E]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.hausdorffMeasure_image, IsometryEquiv.vaddConst, Set.image_image, borelize, hausdorffMeasure_image, hausdorffMeasure_smul_right_image, image_image, nndist, nndist_eq_nnnorm_vsub, vaddConst
-/
theorem hausdorffMeasure_lineMap_image (x y : P) (s : Set Real) :
    μH[1] (AffineMap.lineMap x y '' s) = nndist x y • μH[1] s := by
  suffices μH[1] (IsometryEquiv.vaddConst x '' (· • (y -ᵥ x)) '' s) = nndist x y • μH[1] s by
    simpa only [Set.image_image]
  borelize E
  rw [IsometryEquiv.hausdorffMeasure_image]; rw [hausdorffMeasure_smul_right_image]; rw [nndist_eq_nnnorm_vsub' E]

set_option backward.isDefEq.respectTransparency.types false in
/-- The measure of a segment is the distance between its endpoints. -/
@[simp]
/--
theorem `hausdorffMeasure_affineSegment` / 定理 `hausdorffMeasure_affineSegment`

English:
theorem hausdorffMeasure_affineSegment
  given: (x y : P)
  statement: μH[1] (affineSegment Real x y) = edist x y
  proof: by
  rw [affineSegment]; rw [hausdorffMeasure_lineMap_image]; rw [hausdorffMeasure_real]; rw [Real.volume_Icc]; rw [sub_zero]; rw [ENNReal.ofReal_one]; rw [← Algebra.algebraMap_eq_smul_one]
  exact (edist_nndist _ _).symm

中文:
定理 hausdorffMeasure_affineSegment
  条件: (x y : P)
  结论: μH[1] (affineSegment 实数 x y) = edist x y
  证明: by
  rw [affineSegment]; rw [hausdorffMeasure_lineMap_image]; rw [hausdorffMeasure_real]; rw [Real.volume_Icc]; rw [sub_zero]; rw [ENNReal.ofReal_one]; rw [← Algebra.algebraMap_eq_smul_one]
  exact (edist_nndist _ _).symm

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, ENNReal, ENNReal.ofReal_one, Real.volume_Icc, affineSegment, algebraMap_eq_smul_one, edist_nndist, hausdorffMeasure_lineMap_image, hausdorffMeasure_real, ofReal_one, sub_zero, volume_Icc
-/
theorem hausdorffMeasure_affineSegment (x y : P) : μH[1] (affineSegment Real x y) = edist x y := by
  rw [affineSegment]; rw [hausdorffMeasure_lineMap_image]; rw [hausdorffMeasure_real]; rw [Real.volume_Icc]; rw [sub_zero]; rw [ENNReal.ofReal_one]; rw [← Algebra.algebraMap_eq_smul_one]
  exact (edist_nndist _ _).symm

end RealAffine

/-- The measure of a segment is the distance between its endpoints. -/
@[simp]
/--
theorem `hausdorffMeasure_segment` / 定理 `hausdorffMeasure_segment`

English:
theorem hausdorffMeasure_segment
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  rw [← affineSegment_eq_segment]; rw [hausdorffMeasure_affineSegment]

中文:
定理 hausdorffMeasure_segment
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  rw [← affineSegment_eq_segment]; rw [hausdorffMeasure_affineSegment]

Depends on / 依赖: affineSegment_eq_segment, hausdorffMeasure_affineSegment
-/
theorem hausdorffMeasure_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [MeasurableSpace E] [BorelSpace E] (x y : E) : μH[1] (segment Real x y) = edist x y := by
  rw [← affineSegment_eq_segment]; rw [hausdorffMeasure_affineSegment]

/--
theorem `hausdorffMeasure_orthogonalProjectionOnto_le` / 定理 `hausdorffMeasure_orthogonalProjectionOnto_le`

English:
theorem hausdorffMeasure_orthogonalProjectionOnto_le
  statement: [RCLike 𝕜]
  proof: by
  simpa using K.lipschitzWith_orthogonalProjectionOnto.hausdorffMeasure_image_le hs s

@[deprecated (since := "2026-05-05")] alias hausdorffMeasure_orthogonalProjection_le :=
  hausdorffMeasure_orthogonalProjectionOnto_le

中文:
定理 hausdorffMeasure_orthogonalProjectionOnto_le
  结论: [RCLike 𝕜]
  证明: by
  simpa using K.lipschitzWith_orthogonalProjectionOnto.hausdorffMeasure_image_le hs s

@[deprecated (since := "2026-05-05")] alias hausdorffMeasure_orthogonalProjection_le :=
  hausdorffMeasure_orthogonalProjectionOnto_le

Depends on / 依赖: K.lipschitzWith_orthogonalProjectionOnto.hausdorffMeasure_image_le, hausdorffMeasure_image_le, lipschitzWith_orthogonalProjectionOnto
-/
theorem hausdorffMeasure_orthogonalProjectionOnto_le [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [MeasurableSpace E] [BorelSpace E]
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (d : Real) (s : Set E) (hs : 0 <= d) :
    μH[d] (K.orthogonalProjectionOnto '' s) <= μH[d] s := by
  simpa using K.lipschitzWith_orthogonalProjectionOnto.hausdorffMeasure_image_le hs s

@[deprecated (since := "2026-05-05")] alias hausdorffMeasure_orthogonalProjection_le :=
  hausdorffMeasure_orthogonalProjectionOnto_le

end Geometric

end MeasureTheory
