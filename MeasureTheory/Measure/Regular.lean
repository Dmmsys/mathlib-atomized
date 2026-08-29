/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Regular measures

A measure is `OuterRegular` if the measure of any measurable set `A` is the infimum of `μ U` over
all open sets `U` containing `A`.

A measure is `WeaklyRegular` if it satisfies the following properties:
* it is outer regular;
* it is inner regular for open sets with respect to closed sets: the measure of any open set `U`
  is the supremum of `μ F` over all closed sets `F` contained in `U`.

A measure is `Regular` if it satisfies the following properties:
* it is finite on compact sets;
* it is outer regular;
* it is inner regular for open sets with respect to compact closed sets: the measure of any open
  set `U` is the supremum of `μ K` over all compact sets `K` contained in `U`.

A measure is `InnerRegular` if it is inner regular for measurable sets with respect to compact
sets: the measure of any measurable set `s` is the supremum of `μ K` over all compact
sets contained in `s`.

A measure is `InnerRegularCompactLTTop` if it is inner regular for measurable sets of finite
measure with respect to compact sets: the measure of any measurable set `s` is the supremum
of `μ K` over all compact sets contained in `s`.

There is a reason for this zoo of regularity classes:
* A finite measure on a metric space is always weakly regular. Therefore, in probability theory,
  weakly regular measures play a prominent role.
* In locally compact topological spaces, there are two competing notions of Radon measures: the
  ones that are regular, and the ones that are inner regular. For any of these two notions, there is
  a Riesz representation theorem, and an existence and uniqueness statement for the Haar measure in
  locally compact topological groups. The two notions coincide in sigma-compact spaces, but they
  differ in general, so it is worth having the two of them.
* Both notions of Haar measure satisfy the weaker notion `InnerRegularCompactLTTop`, so it is worth
  trying to express theorems using this weaker notion whenever possible, to make sure that it
  applies to both Haar measures simultaneously.

While traditional textbooks on measure theory on locally compact spaces emphasize regular measures,
more recent textbooks emphasize that inner regular Haar measures are better behaved than regular
Haar measures, so we will develop both notions.

The five conditions above are registered as typeclasses for a measure `μ`, and implications between
them are recorded as instances. For example, in a Hausdorff topological space, regularity implies
weak regularity. Also, regularity or inner regularity both imply `InnerRegularCompactLTTop`.
In a regular locally compact finite measure space, then regularity, inner regularity
and `InnerRegularCompactLTTop` are all equivalent.

In order to avoid code duplication, we also define a measure `μ` to be `InnerRegularWRT` for sets
satisfying a predicate `q` with respect to sets satisfying a predicate `p` if for any set
`U ∈ {U | q U}` and a number `r < μ U` there exists `F ⊆ U` such that `p F` and `r < μ F`.

There are two main nontrivial results in the development below:
* `InnerRegularWRT.measurableSet_of_isOpen` shows that, for an outer regular measure, inner
  regularity for open sets with respect to compact sets or closed sets implies inner regularity for
  all measurable sets of finite measure (with respect to compact sets or closed sets respectively).
* `InnerRegularWRT.weaklyRegular_of_finite` shows that a finite measure which is inner regular for
  open sets with respect to closed sets (for instance a finite measure on a metric space) is weakly
  regular.

All other results are deduced from these ones.

Here is an example showing how regularity and inner regularity may differ even on locally compact
spaces. Consider the group `ℝ × ℝ` where the first factor has the discrete topology and the second
one the usual topology. It is a locally compact Hausdorff topological group, with Haar measure equal
to Lebesgue measure on each vertical fiber. Let us consider the regular version of Haar measure.
Then the set `ℝ × {0}` has infinite measure (by outer regularity), but any compact set it contains
has zero measure (as it is finite). In fact, this set only contains subsets with measure zero or
infinity. The inner regular version of Haar measure, on the other hand, gives zero mass to the
set `ℝ × {0}`.

Another interesting example is the sum of the Dirac masses at rational points on the real line.
It is a σ-finite measure on a locally compact metric space, but it is not outer regular: for
outer regularity, one needs additional locally finite assumptions. On the other hand, it is
inner regular.

Several authors require both regularity and inner regularity for their measures. We have opted
for the more fine-grained definitions above as they apply more generally.

## Main definitions

* `MeasureTheory.Measure.OuterRegular μ`: a typeclass registering that a measure `μ` on a
  topological space is outer regular.
* `MeasureTheory.Measure.Regular μ`: a typeclass registering that a measure `μ` on a topological
  space is regular.
* `MeasureTheory.Measure.WeaklyRegular μ`: a typeclass registering that a measure `μ` on a
  topological space is weakly regular.
* `MeasureTheory.Measure.InnerRegularWRT μ p q`: a non-typeclass predicate saying that a measure `μ`
  is inner regular for sets satisfying `q` with respect to sets satisfying `p`.
* `MeasureTheory.Measure.InnerRegular μ`: a typeclass registering that a measure `μ` on a
  topological space is inner regular for measurable sets with respect to compact sets.
* `MeasureTheory.Measure.InnerRegularCompactLTTop μ`: a typeclass registering that a measure `μ`
  on a topological space is inner regular for measurable sets of finite measure with respect to
  compact sets.

## Main results

### Outer regular measures

* `Set.measure_eq_iInf_isOpen` asserts that, when `μ` is outer regular, the measure of a
  set is the infimum of the measure of open sets containing it.
* `Set.exists_isOpen_lt_of_lt` asserts that, when `μ` is outer regular, for every set `s`
  and `r > μ s` there exists an open superset `U ⊇ s` of measure less than `r`.
* push forward of an outer regular measure is outer regular, and scalar multiplication of a regular
  measure by a finite number is outer regular.

### Weakly regular measures

* `IsOpen.measure_eq_iSup_isClosed` asserts that the measure of an open set is the supremum of
  the measure of closed sets it contains.
* `IsOpen.exists_lt_isClosed`: for an open set `U` and `r < μ U`, there exists a closed `F ⊆ U`
  of measure greater than `r`;
* `MeasurableSet.measure_eq_iSup_isClosed_of_ne_top` asserts that the measure of a measurable set
  of finite measure is the supremum of the measure of closed sets it contains.
* `MeasurableSet.exists_lt_isClosed_of_ne_top` and `MeasurableSet.exists_isClosed_lt_add`:
  a measurable set of finite measure can be approximated by a closed subset (stated as
  `r < μ F` and `μ s < μ F + ε`, respectively).
* `MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure` is an
  instance registering that a finite measure on a metric space is weakly regular (in fact, a
  pseudometrizable space is enough);
* `MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_secondCountable_of_locallyFinite`
  is an instance registering that a locally finite measure on a second countable metric space (or
  even a pseudometrizable space) is weakly regular.

### Regular measures

* `IsOpen.measure_eq_iSup_isCompact` asserts that the measure of an open set is the supremum of
  the measure of compact sets it contains.
* `IsOpen.exists_lt_isCompact`: for an open set `U` and `r < μ U`, there exists a compact `K ⊆ U`
  of measure greater than `r`;
* `MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure` is an
  instance registering that a locally finite measure on a `σ`-compact metric space is regular (in
  fact, an emetric space is enough).

### Inner regular measures

* `MeasurableSet.measure_eq_iSup_isCompact` asserts that the measure of a measurable set is the
  supremum of the measure of compact sets it contains.
* `MeasurableSet.exists_lt_isCompact`: for a measurable set `s` and `r < μ s`, there exists a
  compact `K ⊆ s` of measure greater than `r`;

### Inner regular measures for finite measure sets with respect to compact sets

* `MeasurableSet.measure_eq_iSup_isCompact_of_ne_top` asserts that the measure of a measurable set
  of finite measure is the supremum of the measure of compact sets it contains.
* `MeasurableSet.exists_lt_isCompact_of_ne_top` and `MeasurableSet.exists_isCompact_lt_add`:
  a measurable set of finite measure can be approximated by a compact subset (stated as
  `r < μ K` and `μ s < μ K + ε`, respectively).

## Implementation notes

The main nontrivial statement is `MeasureTheory.Measure.InnerRegular.weaklyRegular_of_finite`,
expressing that in a finite measure space, if every open set can be approximated from inside by
closed sets, then the measure is in fact weakly regular. To prove that we show that any measurable
set can be approximated from inside by closed sets and from outside by open sets. This statement is
proved by measurable induction, starting from open sets and checking that it is stable by taking
complements (this is the point of this condition, being symmetrical between inside and outside) and
countable disjoint unions.

Once this statement is proved, one deduces results for `σ`-finite measures from this statement, by
restricting them to finite measure sets (and proving that this restriction is weakly regular, using
again the same statement).

For non-Hausdorff spaces, one may argue whether the right condition for inner regularity is with
respect to compact sets, or to compact closed sets. For instance,
[Fremlin, *Measure Theory* (volume 4, 411J)][fremlin_vol4] considers measures which are inner
regular with respect to compact closed sets (and calls them *tight*). However, since most of the
literature uses mere compact sets, we have chosen to follow this convention. It doesn't make a
difference in Hausdorff spaces, of course. In locally compact topological groups, the two
conditions coincide, since if a compact set `k` is contained in a measurable set `u`, then the
closure of `k` is a compact closed set still contained in `u`, see
`IsCompact.closure_subset_of_measurableSet_of_group`.

## References

[Halmos, Measure Theory, §52][halmos1950measure]. Note that Halmos uses an unusual definition of
Borel sets (for him, they are elements of the `σ`-algebra generated by compact sets!), so his
proofs or statements do not apply directly.

[Billingsley, Convergence of Probability Measures][billingsley1999]

[Bogachev, Measure Theory, volume 2, Theorem 7.11.1][bogachev2007]
-/

@[expose] public section

open Set Filter ENNReal NNReal TopologicalSpace
open scoped symmDiff Topology

namespace MeasureTheory

namespace Measure

/--
Definition of `InnerRegularWRT` / `InnerRegularWRT` 的定义

English:
definition InnerRegularWRT
  signature: {α} {_ : MeasurableSpace α} (μ : Measure α) (p q : Set α -> Prop)
  body: forall ⦃U⦄, q U -> forall r < μ U, exists K, K subseteq U ∧ p K ∧ r < μ K

中文:
定义 InnerRegularWRT
  签名: {α} {_ : MeasurableSpace α} (μ : Measure α) (p q : Set α -> 命题)
  定义体: forall ⦃U⦄, q U -> forall r < μ U, exists K, K subseteq U ∧ p K ∧ r < μ K

Depends on / 依赖: subseteq
-/
def InnerRegularWRT {α} {_ : MeasurableSpace α} (μ : Measure α) (p q : Set α -> Prop) :=
  forall ⦃U⦄, q U -> forall r < μ U, exists K, K subseteq U ∧ p K ∧ r < μ K

namespace InnerRegularWRT

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {p q : Set α -> Prop} {U : Set α}
  {ε : Real>=0∞}

/--
theorem `measure_eq_iSup` / 定理 `measure_eq_iSup`

English:
theorem measure_eq_iSup
  given: (H : InnerRegularWRT μ p q) (hU : q U)
  proof: by
  refine
    le_antisymm (le_of_forall_lt fun r hr => ?_) (iSup₂_le fun K hK => iSup_le fun _ => μ.mono hK)
  simpa only [lt_iSup_iff, exists_prop] using H hU r hr

中文:
定理 measure_eq_iSup
  条件: (H : InnerRegularWRT μ p q) (hU : q U)
  证明: by
  refine
    le_antisymm (le_of_forall_lt fun r hr => ?_) (iSup₂_le fun K hK => iSup_le fun _ => μ.mono hK)
  simpa only [lt_iSup_iff, exists_prop] using H hU r hr

Depends on / 依赖: exists_prop, iSup_le, le_antisymm, le_of_forall_lt, lt_iSup_iff
-/
theorem measure_eq_iSup (H : InnerRegularWRT μ p q) (hU : q U) :
    μ U = ⨆ (K) (_ : K subseteq U) (_ : p K), μ K := by
  refine
    le_antisymm (le_of_forall_lt fun r hr => ?_) (iSup₂_le fun K hK => iSup_le fun _ => μ.mono hK)
  simpa only [lt_iSup_iff, exists_prop] using H hU r hr

/--
theorem `eq_of_innerRegularWRT_of_forall_eq` / 定理 `eq_of_innerRegularWRT_of_forall_eq`

English:
theorem eq_of_innerRegularWRT_of_forall_eq
  statement: {ν : Measure α} (hμ : μ.InnerRegularWRT p q)
  proof: by
  rw [hμ.measure_eq_iSup hU]; rw [hν.measure_eq_iSup hU]
  congr! 4 with t _ ht2
  exact hμν t ht2

中文:
定理 eq_of_innerRegularWRT_of_forall_eq
  结论: {ν : Measure α} (hμ : μ.InnerRegularWRT p q)
  证明: by
  rw [hμ.measure_eq_iSup hU]; rw [hν.measure_eq_iSup hU]
  congr! 4 with t _ ht2
  exact hμν t ht2

Depends on / 依赖: measure_eq_iSup
-/
theorem eq_of_innerRegularWRT_of_forall_eq {ν : Measure α} (hμ : μ.InnerRegularWRT p q)
    (hν : ν.InnerRegularWRT p q) (hμν : forall U, p U -> μ U = ν U)
    {U : Set α} (hU : q U) : μ U = ν U := by
  rw [hμ.measure_eq_iSup hU]; rw [hν.measure_eq_iSup hU]
  congr! 4 with t _ ht2
  exact hμν t ht2

/--
theorem `exists_subset_lt_add` / 定理 `exists_subset_lt_add`

English:
theorem exists_subset_lt_add
  statement: (H : InnerRegularWRT μ p q) (h0 : p ∅) (hU : q U) (hμU : μ U != ∞)
  proof: by
  rcases eq_or_ne (μ U) 0 with h₀ | h₀
  · refine ⟨∅, empty_subset _, h0, ?_⟩
    rwa [measure_empty, h₀, zero_add, pos_iff_ne_zero]
  · rcases H hU _ (ENNReal.sub_lt_self hμU h₀ hε) with ⟨K, hKU, hKc, hrK⟩
    exact ⟨K, hKU, hKc, ENNReal.lt_add_of_sub_lt_right (Or.inl hμU) hrK⟩

中文:
定理 exists_subset_lt_add
  结论: (H : InnerRegularWRT μ p q) (h0 : p ∅) (hU : q U) (hμU : μ U != ∞)
  证明: by
  rcases eq_or_ne (μ U) 0 with h₀ | h₀
  · refine ⟨∅, empty_subset _, h0, ?_⟩
    rwa [measure_empty, h₀, zero_add, pos_iff_ne_zero]
  · rcases H hU _ (ENNReal.sub_lt_self hμU h₀ hε) with ⟨K, hKU, hKc, hrK⟩
    exact ⟨K, hKU, hKc, ENNReal.lt_add_of_sub_lt_right (Or.inl hμU) hrK⟩

Depends on / 依赖: ENNReal, ENNReal.lt_add_of_sub_lt_right, ENNReal.sub_lt_self, Or.inl, empty_subset, eq_or_ne, lt_add_of_sub_lt_right, measure_empty, pos_iff_ne_zero, sub_lt_self, zero_add
-/
theorem exists_subset_lt_add (H : InnerRegularWRT μ p q) (h0 : p ∅) (hU : q U) (hμU : μ U != ∞)
    (hε : ε != 0) : exists K, K subseteq U ∧ p K ∧ μ U < μ K + ε := by
  rcases eq_or_ne (μ U) 0 with h₀ | h₀
  · refine ⟨∅, empty_subset _, h0, ?_⟩
    rwa [measure_empty, h₀, zero_add, pos_iff_ne_zero]
  · rcases H hU _ (ENNReal.sub_lt_self hμU h₀ hε) with ⟨K, hKU, hKc, hrK⟩
    exact ⟨K, hKU, hKc, ENNReal.lt_add_of_sub_lt_right (Or.inl hμU) hrK⟩

/--
theorem `map` / 定理 `map`

English:
theorem map
  statement: {α β} [MeasurableSpace α] [MeasurableSpace β]
  proof: by
  intro U hU r hr
  rw [map_apply_of_aemeasurable hf (hB₂ _ hU)] at hr
  rcases H (hAB U hU) r hr with ⟨K, hKU, hKc, hK⟩
  refine ⟨f '' K, image_subset_iff.2 hKU, hAB' _ hKc, ?_⟩
  exact hK.trans_le (le_map_apply_image hf _)

中文:
定理 map
  结论: {α β} [MeasurableSpace α] [MeasurableSpace β]
  证明: by
  intro U hU r hr
  rw [map_apply_of_aemeasurable hf (hB₂ _ hU)] at hr
  rcases H (hAB U hU) r hr with ⟨K, hKU, hKc, hK⟩
  refine ⟨f '' K, image_subset_iff.2 hKU, hAB' _ hKc, ?_⟩
  exact hK.trans_le (le_map_apply_image hf _)
-/
protected theorem map {α β} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {pa qa : Set α -> Prop}
    (H : InnerRegularWRT μ pa qa) {f : α -> β} (hf : AEMeasurable f μ) {pb qb : Set β -> Prop}
    (hAB : forall U, qb U -> qa (f ⁻¹' U)) (hAB' : forall K, pa K -> pb (f '' K))
    (hB₂ : forall U, qb U -> MeasurableSet U) :
    InnerRegularWRT (map f μ) pb qb := by
  intro U hU r hr
  rw [map_apply_of_aemeasurable hf (hB₂ _ hU)] at hr
  rcases H (hAB U hU) r hr with ⟨K, hKU, hKc, hK⟩
  refine ⟨f '' K, image_subset_iff.2 hKU, hAB' _ hKc, ?_⟩
  exact hK.trans_le (le_map_apply_image hf _)

/--
theorem `map'` / 定理 `map'`

English:
theorem map'
  statement: {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {pa qa : Set α -> Prop}
  proof: by
  intro U hU r hr
  rw [f.map_apply U] at hr
  rcases H (hAB U hU) r hr with ⟨K, hKU, hKc, hK⟩
  refine ⟨f '' K, image_subset_iff.2 hKU, hAB' _ hKc, ?_⟩
  rwa [f.map_apply, f.preimage_image]

中文:
定理 map'
  结论: {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {pa qa : Set α -> 命题}
  证明: by
  intro U hU r hr
  rw [f.map_apply U] at hr
  rcases H (hAB U hU) r hr with ⟨K, hKU, hKc, hK⟩
  refine ⟨f '' K, image_subset_iff.2 hKU, hAB' _ hKc, ?_⟩
  rwa [f.map_apply, f.preimage_image]

Depends on / 依赖: f.map_apply, f.preimage_image, image_subset_iff, map_apply, preimage_image
-/
theorem map' {α β} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {pa qa : Set α -> Prop}
    (H : InnerRegularWRT μ pa qa) (f : α ≃ᵐ β) {pb qb : Set β -> Prop}
    (hAB : forall U, qb U -> qa (f ⁻¹' U)) (hAB' : forall K, pa K -> pb (f '' K)) :
    InnerRegularWRT (map f μ) pb qb := by
  intro U hU r hr
  rw [f.map_apply U] at hr
  rcases H (hAB U hU) r hr with ⟨K, hKU, hKc, hK⟩
  refine ⟨f '' K, image_subset_iff.2 hKU, hAB' _ hKc, ?_⟩
  rwa [f.map_apply, f.preimage_image]

/--
theorem `comap` / 定理 `comap`

English:
theorem comap
  statement: {α β} [MeasurableSpace α] {mβ : MeasurableSpace β}
  proof: by
  intro U hU r hr
  rw [hf.comap_apply] at hr
  obtain ⟨K, hKU, hK, hμU⟩ := H (hAB U hU) r hr
  have hKrange := hKU.trans (image_subset_range _ _)
  refine ⟨f ⁻¹' K, ?_, hAB' K hKrange hK, ?_⟩
  · rw [← hf.injective.preimage_image U]; exact preimage_mono hKU
  · rwa [hf.comap_apply, image_preimag

中文:
定理 comap
  结论: {α β} [MeasurableSpace α] {mβ : MeasurableSpace β}
  证明: by
  intro U hU r hr
  rw [hf.comap_apply] at hr
  obtain ⟨K, hKU, hK, hμU⟩ := H (hAB U hU) r hr
  have hKrange := hKU.trans (image_subset_range _ _)
  refine ⟨f ⁻¹' K, ?_, hAB' K hKrange hK, ?_⟩
  · rw [← hf.injective.preimage_image U]; exact preimage_mono hKU
  · rwa [hf.comap_apply, image_preimag
-/
protected theorem comap {α β} [MeasurableSpace α] {mβ : MeasurableSpace β}
    {μ : Measure β} {pa qa : Set α -> Prop} {pb qb : Set β -> Prop}
    (H : InnerRegularWRT μ pb qb) {f : α -> β} (hf : MeasurableEmbedding f)
    (hAB : forall U, qa U -> qb (f '' U)) (hAB' : forall K subseteq range f, pb K -> pa (f ⁻¹' K)) :
    (μ.comap f).InnerRegularWRT pa qa := by
  intro U hU r hr
  rw [hf.comap_apply] at hr
  obtain ⟨K, hKU, hK, hμU⟩ := H (hAB U hU) r hr
  have hKrange := hKU.trans (image_subset_range _ _)
  refine ⟨f ⁻¹' K, ?_, hAB' K hKrange hK, ?_⟩
  · rw [← hf.injective.preimage_image U]; exact preimage_mono hKU
  · rwa [hf.comap_apply, image_preimage_eq_iff.mpr hKrange]

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: (H : InnerRegularWRT μ p q) (c : Real>=0∞)
  statement: InnerRegularWRT (c • μ) p q
  proof: by
  intro U hU r hr
  rw [smul_apply]; rw [H.measure_eq_iSup hU]; rw [smul_eq_mul] at hr
  simpa only [ENNReal.mul_iSup, lt_iSup_iff, exists_prop] using! hr

中文:
定理 smul
  条件: (H : InnerRegularWRT μ p q) (c : 实数>=0∞)
  结论: InnerRegularWRT (c • μ) p q
  证明: by
  intro U hU r hr
  rw [smul_apply]; rw [H.measure_eq_iSup hU]; rw [smul_eq_mul] at hr
  simpa only [ENNReal.mul_iSup, lt_iSup_iff, exists_prop] using! hr

Depends on / 依赖: ENNReal, ENNReal.mul_iSup, H.measure_eq_iSup, exists_prop, lt_iSup_iff, measure_eq_iSup, mul_iSup, smul_apply, smul_eq_mul
-/
theorem smul (H : InnerRegularWRT μ p q) (c : Real>=0∞) : InnerRegularWRT (c • μ) p q := by
  intro U hU r hr
  rw [smul_apply]; rw [H.measure_eq_iSup hU]; rw [smul_eq_mul] at hr
  simpa only [ENNReal.mul_iSup, lt_iSup_iff, exists_prop] using! hr

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: {q' : Set α -> Prop} (H : InnerRegularWRT μ p q) (H' : InnerRegularWRT μ q q')
  proof: by
  intro U hU r hr
  rcases H' hU r hr with ⟨F, hFU, hqF, hF⟩; rcases H hqF _ hF with ⟨K, hKF, hpK, hrK⟩
  exact ⟨K, hKF.trans hFU, hpK, hrK⟩

中文:
定理 trans
  条件: {q' : Set α -> 命题} (H : InnerRegularWRT μ p q) (H' : InnerRegularWRT μ q q')
  证明: by
  intro U hU r hr
  rcases H' hU r hr with ⟨F, hFU, hqF, hF⟩; rcases H hqF _ hF with ⟨K, hKF, hpK, hrK⟩
  exact ⟨K, hKF.trans hFU, hpK, hrK⟩

Depends on / 依赖: hKF.trans
-/
theorem trans {q' : Set α -> Prop} (H : InnerRegularWRT μ p q) (H' : InnerRegularWRT μ q q') :
    InnerRegularWRT μ p q' := by
  intro U hU r hr
  rcases H' hU r hr with ⟨F, hFU, hqF, hF⟩; rcases H hqF _ hF with ⟨K, hKF, hpK, hrK⟩
  exact ⟨K, hKF.trans hFU, hpK, hrK⟩

/--
theorem `rfl` / 定理 `rfl`

English:
theorem rfl
  given: {p : Set α -> Prop}
  statement: InnerRegularWRT μ p p
  proof: fun U hU _r hr => ⟨U, Subset.rfl, hU, hr⟩

中文:
定理 rfl
  条件: {p : Set α -> 命题}
  结论: InnerRegularWRT μ p p
  证明: fun U hU _r hr => ⟨U, Subset.rfl, hU, hr⟩

Depends on / 依赖: Subset, Subset.rfl
-/
theorem rfl {p : Set α -> Prop} : InnerRegularWRT μ p p :=
  fun U hU _r hr => ⟨U, Subset.rfl, hU, hr⟩

/--
theorem `of_imp` / 定理 `of_imp`

English:
theorem of_imp
  given: (h : forall s, q s -> p s)
  statement: InnerRegularWRT μ p q
  proof: fun U hU _ hr => ⟨U, Subset.rfl, h U hU, hr⟩

中文:
定理 of_imp
  条件: (h : 对任意 s, q s -> p s)
  结论: InnerRegularWRT μ p q
  证明: fun U hU _ hr => ⟨U, Subset.rfl, h U hU, hr⟩

Depends on / 依赖: Subset, Subset.rfl
-/
theorem of_imp (h : forall s, q s -> p s) : InnerRegularWRT μ p q :=
  fun U hU _ hr => ⟨U, Subset.rfl, h U hU, hr⟩

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  statement: {p' q' : Set α -> Prop} (H : InnerRegularWRT μ p q)
  proof: .trans (of_imp h) .trans H of_imp h'

中文:
定理 mono
  结论: {p' q' : Set α -> 命题} (H : InnerRegularWRT μ p q)
  证明: .trans (of_imp h) .trans H of_imp h'

Depends on / 依赖: of_imp
-/
theorem mono {p' q' : Set α -> Prop} (H : InnerRegularWRT μ p q)
    (h : forall s, q' s -> q s) (h' : forall s, p s -> p' s) : InnerRegularWRT μ p' q' :=
.trans (of_imp h) .trans H of_imp h'

end InnerRegularWRT

variable {α β : Type*} [MeasurableSpace α] {μ : Measure α}

section Classes

variable [TopologicalSpace α]

/--
Definition of `OuterRegular` / `OuterRegular` 的定义

English:
class OuterRegular
  parameters: (μ : Measure α)
  axioms and operations (1):
    - outerRegular : forall ⦃A : Set α⦄, MeasurableSet A -> forall r > μ A, exists U, U ⊇ A ∧ IsOpen U ∧ μ U < r

中文:
类 OuterRegular
  参数: (μ : Measure α)
  公理与运算 (1 个):
    - outerRegular : 对任意 ⦃A : Set α⦄, MeasurableSet A -> 对任意 r > μ A, 存在 U, U ⊇ A ∧ IsOpen U ∧ μ U < r
-/
class OuterRegular (μ : Measure α) : Prop where
  protected outerRegular :
    forall ⦃A : Set α⦄, MeasurableSet A -> forall r > μ A, exists U, U ⊇ A ∧ IsOpen U ∧ μ U < r

/--
Definition of `Regular` / `Regular` 的定义

English:
class Regular
  parameters: (μ : Measure α)
  extends: IsFiniteMeasureOnCompacts μ, OuterRegular μ
  axioms and operations (1):
    - innerRegular : InnerRegularWRT μ IsCompact IsOpen

中文:
类 Regular
  参数: (μ : Measure α)
  继承: IsFiniteMeasureOnCompacts μ, OuterRegular μ
  公理与运算 (1 个):
    - innerRegular : InnerRegularWRT μ IsCompact IsOpen
-/
class Regular (μ : Measure α) : Prop extends IsFiniteMeasureOnCompacts μ, OuterRegular μ where
  innerRegular : InnerRegularWRT μ IsCompact IsOpen

/--
Definition of `WeaklyRegular` / `WeaklyRegular` 的定义

English:
class WeaklyRegular
  parameters: (μ : Measure α)
  extends: OuterRegular μ
  axioms and operations (1):
    - innerRegular : InnerRegularWRT μ IsClosed IsOpen

中文:
类 WeaklyRegular
  参数: (μ : Measure α)
  继承: OuterRegular μ
  公理与运算 (1 个):
    - innerRegular : InnerRegularWRT μ IsClosed IsOpen
-/
class WeaklyRegular (μ : Measure α) : Prop extends OuterRegular μ where
  protected innerRegular : InnerRegularWRT μ IsClosed IsOpen

/--
Definition of `InnerRegular` / `InnerRegular` 的定义

English:
class InnerRegular
  parameters: (μ : Measure α)
  axioms and operations (1):
    - innerRegular : InnerRegularWRT μ IsCompact MeasurableSet

中文:
类 InnerRegular
  参数: (μ : Measure α)
  公理与运算 (1 个):
    - innerRegular : InnerRegularWRT μ IsCompact MeasurableSet
-/
class InnerRegular (μ : Measure α) : Prop where
  protected innerRegular : InnerRegularWRT μ IsCompact MeasurableSet

/--
Definition of `InnerRegularCompactLTTop` / `InnerRegularCompactLTTop` 的定义

English:
class InnerRegularCompactLTTop
  parameters: (μ : Measure α)
  axioms and operations (1):
    - innerRegular : InnerRegularWRT μ IsCompact (fun s => MeasurableSet s ∧ μ s != ∞)

中文:
类 InnerRegularCompactLTTop
  参数: (μ : Measure α)
  公理与运算 (1 个):
    - innerRegular : InnerRegularWRT μ IsCompact (fun s => MeasurableSet s ∧ μ s != ∞)
-/
class InnerRegularCompactLTTop (μ : Measure α) : Prop where
  protected innerRegular : InnerRegularWRT μ IsCompact (fun s => MeasurableSet s ∧ μ s != ∞)

-- see Note [lower instance priority]
/-- A regular measure is weakly regular in an R₁ space. -/
instance (priority := 100) Regular.weaklyRegular [R1Space α] [Regular μ] :
    WeaklyRegular μ where
  innerRegular := fun _U hU r hr =>
    let ⟨K, KU, K_comp, hK⟩ := Regular.innerRegular hU r hr
    ⟨closure K, K_comp.closure_subset_of_isOpen hU KU, isClosed_closure,
      hK.trans_le (measure_mono subset_closure)⟩

end Classes

namespace OuterRegular

variable [TopologicalSpace α]

/--
Instance `zero` / 实例 `zero`

English:
instance zero
  signature: : OuterRegular (0 : Measure α)
  body: ⟨fun A _ _r hr => ⟨univ, subset_univ A, isOpen_univ, hr⟩⟩

中文:
实例 zero
  签名: : OuterRegular (0 : Measure α)
  定义体: ⟨fun A _ _r hr => ⟨univ, subset_univ A, isOpen_univ, hr⟩⟩

Depends on / 依赖: isOpen_univ, subset_univ
-/
instance zero : OuterRegular (0 : Measure α) :=
  ⟨fun A _ _r hr => ⟨univ, subset_univ A, isOpen_univ, hr⟩⟩

/--
theorem `_root_.Set.exists_isOpen_lt_of_lt` / 定理 `_root_.Set.exists_isOpen_lt_of_lt`

English:
theorem _root_.Set.exists_isOpen_lt_of_lt
  given: [OuterRegular μ] (A : Set α) (r : Real>=0∞) (hr : μ A < r)
  proof: by
  rcases OuterRegular.outerRegular (measurableSet_toMeasurable μ A) r
      (by rwa [measure_toMeasurable]) with
    ⟨U, hAU, hUo, hU⟩
  exact ⟨U, (subset_toMeasurable _ _).trans hAU, hUo, hU⟩

中文:
定理 _root_.Set.exists_isOpen_lt_of_lt
  条件: [OuterRegular μ] (A : Set α) (r : 实数>=0∞) (hr : μ A < r)
  证明: by
  rcases OuterRegular.outerRegular (measurableSet_toMeasurable μ A) r
      (by rwa [measure_toMeasurable]) with
    ⟨U, hAU, hUo, hU⟩
  exact ⟨U, (subset_toMeasurable _ _).trans hAU, hUo, hU⟩

Depends on / 依赖: OuterRegular, OuterRegular.outerRegular, measurableSet_toMeasurable, measure_toMeasurable, outerRegular, subset_toMeasurable
-/
theorem _root_.Set.exists_isOpen_lt_of_lt [OuterRegular μ] (A : Set α) (r : Real>=0∞) (hr : μ A < r) :
    exists U, U ⊇ A ∧ IsOpen U ∧ μ U < r := by
  rcases OuterRegular.outerRegular (measurableSet_toMeasurable μ A) r
      (by rwa [measure_toMeasurable]) with
    ⟨U, hAU, hUo, hU⟩
  exact ⟨U, (subset_toMeasurable _ _).trans hAU, hUo, hU⟩

/--
theorem `_root_.Set.measure_eq_iInf_isOpen` / 定理 `_root_.Set.measure_eq_iInf_isOpen`

English:
theorem _root_.Set.measure_eq_iInf_isOpen
  given: (A : Set α) (μ : Measure α) [OuterRegular μ]
  proof: by
  refine le_antisymm (le_iInf₂ fun s hs => le_iInf fun _ => μ.mono hs) ?_
  refine le_of_forall_gt fun r hr => ?_
  simpa only [iInf_lt_iff, exists_prop] using A.exists_isOpen_lt_of_lt r hr

中文:
定理 _root_.Set.measure_eq_iInf_isOpen
  条件: (A : Set α) (μ : Measure α) [OuterRegular μ]
  证明: by
  refine le_antisymm (le_iInf₂ fun s hs => le_iInf fun _ => μ.mono hs) ?_
  refine le_of_forall_gt fun r hr => ?_
  simpa only [iInf_lt_iff, exists_prop] using A.exists_isOpen_lt_of_lt r hr

Depends on / 依赖: A.exists_isOpen_lt_of_lt, exists_isOpen_lt_of_lt, exists_prop, iInf_lt_iff, le_antisymm, le_iInf, le_of_forall_gt
-/
theorem _root_.Set.measure_eq_iInf_isOpen (A : Set α) (μ : Measure α) [OuterRegular μ] :
    μ A = ⨅ (U : Set α) (_ : A subseteq U) (_ : IsOpen U), μ U := by
  refine le_antisymm (le_iInf₂ fun s hs => le_iInf fun _ => μ.mono hs) ?_
  refine le_of_forall_gt fun r hr => ?_
  simpa only [iInf_lt_iff, exists_prop] using A.exists_isOpen_lt_of_lt r hr

/--
theorem `_root_.Set.exists_isOpen_lt_add` / 定理 `_root_.Set.exists_isOpen_lt_add`

English:
theorem _root_.Set.exists_isOpen_lt_add
  statement: [OuterRegular μ] (A : Set α) (hA : μ A != ∞) {ε : Real>=0∞}
  proof: A.exists_isOpen_lt_of_lt _ (ENNReal.lt_add_right hA hε)

中文:
定理 _root_.Set.exists_isOpen_lt_add
  结论: [OuterRegular μ] (A : Set α) (hA : μ A != ∞) {ε : 实数>=0∞}
  证明: A.exists_isOpen_lt_of_lt _ (ENNReal.lt_add_right hA hε)

Depends on / 依赖: A.exists_isOpen_lt_of_lt, ENNReal, ENNReal.lt_add_right, exists_isOpen_lt_of_lt, lt_add_right
-/
theorem _root_.Set.exists_isOpen_lt_add [OuterRegular μ] (A : Set α) (hA : μ A != ∞) {ε : Real>=0∞}
    (hε : ε != 0) : exists U, U ⊇ A ∧ IsOpen U ∧ μ U < μ A + ε :=
  A.exists_isOpen_lt_of_lt _ (ENNReal.lt_add_right hA hε)

/--
theorem `_root_.Set.exists_isOpen_le_add` / 定理 `_root_.Set.exists_isOpen_le_add`

English:
theorem _root_.Set.exists_isOpen_le_add
  statement: (A : Set α) (μ : Measure α) [OuterRegular μ] {ε : Real>=0∞}
  proof: by
  rcases eq_or_ne (μ A) ∞ with (H | H)
  · exact ⟨univ, subset_univ _, isOpen_univ, by simp only [H, _root_.top_add, le_top]⟩
  · rcases A.exists_isOpen_lt_add H hε with ⟨U, AU, U_open, hU⟩
    exact ⟨U, AU, U_open, hU.le⟩

中文:
定理 _root_.Set.exists_isOpen_le_add
  结论: (A : Set α) (μ : Measure α) [OuterRegular μ] {ε : 实数>=0∞}
  证明: by
  rcases eq_or_ne (μ A) ∞ with (H | H)
  · exact ⟨univ, subset_univ _, isOpen_univ, by simp only [H, _root_.top_add, le_top]⟩
  · rcases A.exists_isOpen_lt_add H hε with ⟨U, AU, U_open, hU⟩
    exact ⟨U, AU, U_open, hU.le⟩

Depends on / 依赖: A.exists_isOpen_lt_add, U_open, _root_, _root_.top_add, eq_or_ne, exists_isOpen_lt_add, hU.le, isOpen_univ, le_top, subset_univ, top_add
-/
theorem _root_.Set.exists_isOpen_le_add (A : Set α) (μ : Measure α) [OuterRegular μ] {ε : Real>=0∞}
    (hε : ε != 0) : exists U, U ⊇ A ∧ IsOpen U ∧ μ U <= μ A + ε := by
  rcases eq_or_ne (μ A) ∞ with (H | H)
  · exact ⟨univ, subset_univ _, isOpen_univ, by simp only [H, _root_.top_add, le_top]⟩
  · rcases A.exists_isOpen_lt_add H hε with ⟨U, AU, U_open, hU⟩
    exact ⟨U, AU, U_open, hU.le⟩

/--
theorem `_root_.MeasurableSet.exists_isOpen_sdiff_lt` / 定理 `_root_.MeasurableSet.exists_isOpen_sdiff_lt`

English:
theorem _root_.MeasurableSet.exists_isOpen_sdiff_lt
  statement: [OuterRegular μ] {A : Set α}
  proof: by
  rcases A.exists_isOpen_lt_add hA' hε with ⟨U, hAU, hUo, hU⟩
  use U, hAU, hUo, hU.trans_le le_top
  exact measure_sdiff_lt_of_lt_add hA.nullMeasurableSet hAU hA' hU

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isOpen_diff_lt := _root_.MeasurableSet.exists_isOpen_sdif

中文:
定理 _root_.MeasurableSet.exists_isOpen_sdiff_lt
  结论: [OuterRegular μ] {A : Set α}
  证明: by
  rcases A.exists_isOpen_lt_add hA' hε with ⟨U, hAU, hUo, hU⟩
  use U, hAU, hUo, hU.trans_le le_top
  exact measure_sdiff_lt_of_lt_add hA.nullMeasurableSet hAU hA' hU

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isOpen_diff_lt := _root_.MeasurableSet.exists_isOpen_sdif

Depends on / 依赖: A.exists_isOpen_lt_add, exists_isOpen_lt_add, hA.nullMeasurableSet, hU.trans_le, le_top, measure_sdiff_lt_of_lt_add, nullMeasurableSet, trans_le
-/
theorem _root_.MeasurableSet.exists_isOpen_sdiff_lt [OuterRegular μ] {A : Set α}
    (hA : MeasurableSet A) (hA' : μ A != ∞) {ε : Real>=0∞} (hε : ε != 0) :
    exists U, U ⊇ A ∧ IsOpen U ∧ μ U < ∞ ∧ μ (U \ A) < ε := by
  rcases A.exists_isOpen_lt_add hA' hε with ⟨U, hAU, hUo, hU⟩
  use U, hAU, hUo, hU.trans_le le_top
  exact measure_sdiff_lt_of_lt_add hA.nullMeasurableSet hAU hA' hU

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isOpen_diff_lt := _root_.MeasurableSet.exists_isOpen_sdiff_lt

/--
theorem `map` / 定理 `map`

English:
theorem map
  statement: [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β]
  proof: by
  refine ⟨fun A hA r hr => ?_⟩
  rw [map_apply f.measurable hA]; rw [← f.image_symm] at hr
  rcases Set.exists_isOpen_lt_of_lt _ r hr with ⟨U, hAU, hUo, hU⟩
  have : IsOpen (f.symm ⁻¹' U) := hUo.preimage f.symm.continuous
  refine ⟨f.symm ⁻¹' U, image_subset_iff.1 hAU, this, ?_⟩
  rwa [map_apply 

中文:
定理 map
  结论: [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β]
  证明: by
  refine ⟨fun A hA r hr => ?_⟩
  rw [map_apply f.measurable hA]; rw [← f.image_symm] at hr
  rcases Set.exists_isOpen_lt_of_lt _ r hr with ⟨U, hAU, hUo, hU⟩
  have : IsOpen (f.symm ⁻¹' U) := hUo.preimage f.symm.continuous
  refine ⟨f.symm ⁻¹' U, image_subset_iff.1 hAU, this, ?_⟩
  rwa [map_apply 
-/
protected theorem map [OpensMeasurableSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] (f : α ≃ₜ β) (μ : Measure α) [OuterRegular μ] :
    (Measure.map f μ).OuterRegular := by
  refine ⟨fun A hA r hr => ?_⟩
  rw [map_apply f.measurable hA]; rw [← f.image_symm] at hr
  rcases Set.exists_isOpen_lt_of_lt _ r hr with ⟨U, hAU, hUo, hU⟩
  have : IsOpen (f.symm ⁻¹' U) := hUo.preimage f.symm.continuous
  refine ⟨f.symm ⁻¹' U, image_subset_iff.1 hAU, this, ?_⟩
  rwa [map_apply f.measurable this.measurableSet, f.preimage_symm, f.preimage_image]

/--
theorem `comap'` / 定理 `comap'`

English:
theorem comap'
  statement: {mβ : MeasurableSpace β} [TopologicalSpace β] (μ : Measure β) [OuterRegular μ]
  proof: by
    rw [f_me.comap_apply] at hr
    obtain ⟨U, hUA, Uopen, hμU⟩ := OuterRegular.outerRegular (f_me.measurableSet_image' hA) r hr
    refine ⟨f ⁻¹' U, by rwa [ge_iff_le, ← image_subset_iff], Uopen.preimage f_cont, ?_⟩
    rw [f_me.comap_apply]
    exact (measure_mono (image_preimage_subset _ _)).t

中文:
定理 comap'
  结论: {mβ : MeasurableSpace β} [TopologicalSpace β] (μ : Measure β) [OuterRegular μ]
  证明: by
    rw [f_me.comap_apply] at hr
    obtain ⟨U, hUA, Uopen, hμU⟩ := OuterRegular.outerRegular (f_me.measurableSet_image' hA) r hr
    refine ⟨f ⁻¹' U, by rwa [ge_iff_le, ← image_subset_iff], Uopen.preimage f_cont, ?_⟩
    rw [f_me.comap_apply]
    exact (measure_mono (image_preimage_subset _ _)).t

Depends on / 依赖: OuterRegular, OuterRegular.outerRegular, Uopen.preimage, comap_apply, f_cont, f_me, f_me.comap_apply, f_me.measurableSet_image, ge_iff_le, image_preimage_subset, image_subset_iff, measurableSet_image, measure_mono, outerRegular, preimage, trans_lt
-/
theorem comap' {mβ : MeasurableSpace β} [TopologicalSpace β] (μ : Measure β) [OuterRegular μ]
    {f : α -> β} (f_cont : Continuous f) (f_me : MeasurableEmbedding f) :
    (μ.comap f).OuterRegular where
  outerRegular A hA r hr := by
    rw [f_me.comap_apply] at hr
    obtain ⟨U, hUA, Uopen, hμU⟩ := OuterRegular.outerRegular (f_me.measurableSet_image' hA) r hr
    refine ⟨f ⁻¹' U, by rwa [ge_iff_le, ← image_subset_iff], Uopen.preimage f_cont, ?_⟩
    rw [f_me.comap_apply]
    exact (measure_mono (image_preimage_subset _ _)).trans_lt hμU

/--
theorem `comap` / 定理 `comap`

English:
theorem comap
  statement: [BorelSpace α] {mβ : MeasurableSpace β} [TopologicalSpace β] [BorelSpace β]
  proof: OuterRegular.comap' μ f.continuous f.measurableEmbedding

中文:
定理 comap
  结论: [BorelSpace α] {mβ : MeasurableSpace β} [TopologicalSpace β] [BorelSpace β]
  证明: OuterRegular.comap' μ f.continuous f.measurableEmbedding
-/
protected theorem comap [BorelSpace α] {mβ : MeasurableSpace β} [TopologicalSpace β] [BorelSpace β]
    (μ : Measure β) [OuterRegular μ] (f : α ≃ₜ β) : (μ.comap f).OuterRegular :=
  OuterRegular.comap' μ f.continuous f.measurableEmbedding

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: (μ : Measure α) [OuterRegular μ] {x : Real>=0∞} (hx : x != ∞)
  proof: by
  rcases eq_or_ne x 0 with (rfl | h0)
  · rw [zero_smul]
    exact OuterRegular.zero
  · refine ⟨fun A _ r hr => ?_⟩
    rw [smul_apply]; rw [A.measure_eq_iInf_isOpen]; rw [smul_eq_mul] at hr
    simpa only [ENNReal.mul_iInf_of_ne h0 hx, gt_iff_lt, iInf_lt_iff, exists_prop] using! hr

中文:
定理 smul
  条件: (μ : Measure α) [OuterRegular μ] {x : 实数>=0∞} (hx : x != ∞)
  证明: by
  rcases eq_or_ne x 0 with (rfl | h0)
  · rw [zero_smul]
    exact OuterRegular.zero
  · refine ⟨fun A _ r hr => ?_⟩
    rw [smul_apply]; rw [A.measure_eq_iInf_isOpen]; rw [smul_eq_mul] at hr
    simpa only [ENNReal.mul_iInf_of_ne h0 hx, gt_iff_lt, iInf_lt_iff, exists_prop] using! hr
-/
protected theorem smul (μ : Measure α) [OuterRegular μ] {x : Real>=0∞} (hx : x != ∞) :
    (x • μ).OuterRegular := by
  rcases eq_or_ne x 0 with (rfl | h0)
  · rw [zero_smul]
    exact OuterRegular.zero
  · refine ⟨fun A _ r hr => ?_⟩
    rw [smul_apply]; rw [A.measure_eq_iInf_isOpen]; rw [smul_eq_mul] at hr
    simpa only [ENNReal.mul_iInf_of_ne h0 hx, gt_iff_lt, iInf_lt_iff, exists_prop] using! hr

/--
Instance `smul_nnreal` / 实例 `smul_nnreal`

English:
instance smul_nnreal
  signature: (μ : Measure α) [OuterRegular μ] (c : Real>=0)
  body: OuterRegular.smul μ coe_ne_top

中文:
实例 smul_nnreal
  签名: (μ : Measure α) [OuterRegular μ] (c : 实数>=0)
  定义体: OuterRegular.smul μ coe_ne_top

Depends on / 依赖: OuterRegular, OuterRegular.smul, coe_ne_top
-/
instance smul_nnreal (μ : Measure α) [OuterRegular μ] (c : Real>=0) :
    OuterRegular (c • μ) :=
  OuterRegular.smul μ coe_ne_top

open scoped Function in -- required for scoped `on` notation
/--
lemma `of_restrict` / 引理 `of_restrict`

English:
lemma of_restrict
  statement: [OpensMeasurableSpace α] {μ : Measure α} {s : Nat -> Set α}
  proof: by
  refine ⟨fun A hA r hr => ?_⟩
  have HA : μ A < ∞ := lt_of_lt_of_le hr le_top
  have hm : forall n, MeasurableSet (s n) := fun n => (h' n).measurableSet
  -- Note that `A = ⋃ n, A ∩ disjointed s n`. We replace `A` with this sequence.
  obtain ⟨A, hAm, hAs, hAd, rfl⟩ :
    exists A' : Nat -> Set 

中文:
引理 of_restrict
  结论: [OpensMeasurableSpace α] {μ : Measure α} {s : 自然数 -> Set α}
  证明: by
  refine ⟨fun A hA r hr => ?_⟩
  have HA : μ A < ∞ := lt_of_lt_of_le hr le_top
  have hm : forall n, MeasurableSet (s n) := fun n => (h' n).measurableSet
  -- Note that `A = ⋃ n, A ∩ disjointed s n`. We replace `A` with this sequence.
  obtain ⟨A, hAm, hAs, hAd, rfl⟩ :
    exists A' : Nat -> Set 

Depends on / 依赖: MeasurableSet, le_top, lt_of_lt_of_le, measurableSet
-/
lemma of_restrict [OpensMeasurableSpace α] {μ : Measure α} {s : Nat -> Set α}
    (h : forall n, OuterRegular (μ.restrict (s n))) (h' : forall n, IsOpen (s n)) (h'' : univ subseteq ⋃ n, s n) :
    OuterRegular μ := by
  refine ⟨fun A hA r hr => ?_⟩
  have HA : μ A < ∞ := lt_of_lt_of_le hr le_top
  have hm : forall n, MeasurableSet (s n) := fun n => (h' n).measurableSet
  -- Note that `A = ⋃ n, A ∩ disjointed s n`. We replace `A` with this sequence.
  obtain ⟨A, hAm, hAs, hAd, rfl⟩ :
    exists A' : Nat -> Set α,
      (forall n, MeasurableSet (A' n)) ∧
        (forall n, A' n subseteq s n) ∧ Pairwise (Disjoint on A') ∧ A = ⋃ n, A' n := by
    refine
      ⟨fun n => A inter disjointed s n, fun n => hA.inter (MeasurableSet.disjointed hm _), fun n =>
        inter_subset_right.trans (disjointed_subset _ _),
        (disjoint_disjointed s).mono fun k l hkl => hkl.mono inf_le_right inf_le_right, ?_⟩
    rw [← inter_iUnion]; rw [iUnion_disjointed]; rw [univ_subset_iff.mp h'']; rw [inter_univ]
  rcases ENNReal.exists_pos_sum_of_countable' (tsub_pos_iff_lt.2 hr).ne' Nat with ⟨δ, δ0, hδε⟩
  rw [lt_tsub_iff_right]; rw [add_comm] at hδε
  have : forall n, exists U ⊇ A n, IsOpen U ∧ μ U < μ (A n) + δ n := by
    intro n
    have H₁ : forall t, μ.restrict (s n) t = μ (t inter s n) := fun t => restrict_apply' (hm n)
    have Ht : μ.restrict (s n) (A n) != ∞ := by
      rw [H₁]
      exact ((measure_mono (inter_subset_left.trans (subset_iUnion A n))).trans_lt HA).ne
    rcases (A n).exists_isOpen_lt_add Ht (δ0 n).ne' with ⟨U, hAU, hUo, hU⟩
    rw [H₁]; rw [H₁]; rw [inter_eq_self_of_subset_left (hAs _)] at hU
    exact ⟨U inter s n, subset_inter hAU (hAs _), hUo.inter (h' n), hU⟩
  choose U hAU hUo hU using this
  refine ⟨⋃ n, U n, iUnion_mono hAU, isOpen_iUnion hUo, ?_⟩
  calc
    μ (⋃ n, U n) <= ∑' n, μ (U n) := measure_iUnion_le _
    _ <= ∑' n, (μ (A n) + δ n) := ENNReal.tsum_le_tsum fun n => (hU n).le
    _ = ∑' n, μ (A n) + ∑' n, δ n := ENNReal.tsum_add
    _ = μ (⋃ n, A n) + ∑' n, δ n := (congr_arg₂ (· + ·) (measure_iUnion hAd hAm).symm rfl)
    _ < r := hδε

/--
lemma `measure_closure_eq_of_isCompact` / 引理 `measure_closure_eq_of_isCompact`

English:
lemma measure_closure_eq_of_isCompact
  statement: [R1Space α] [OuterRegular μ]
  proof: by
  apply le_antisymm ?_ (measure_mono subset_closure)
  simp only [measure_eq_iInf_isOpen k, le_iInf_iff]
  intro u ku u_open
  exact measure_mono (hk.closure_subset_of_isOpen u_open ku)

中文:
引理 measure_closure_eq_of_isCompact
  结论: [R1Space α] [OuterRegular μ]
  证明: by
  apply le_antisymm ?_ (measure_mono subset_closure)
  simp only [measure_eq_iInf_isOpen k, le_iInf_iff]
  intro u ku u_open
  exact measure_mono (hk.closure_subset_of_isOpen u_open ku)

Depends on / 依赖: closure_subset_of_isOpen, hk.closure_subset_of_isOpen, le_antisymm, le_iInf_iff, measure_eq_iInf_isOpen, measure_mono, subset_closure, u_open
-/
lemma measure_closure_eq_of_isCompact [R1Space α] [OuterRegular μ]
    {k : Set α} (hk : IsCompact k) : μ (closure k) = μ k := by
  apply le_antisymm ?_ (measure_mono subset_closure)
  simp only [measure_eq_iInf_isOpen k, le_iInf_iff]
  intro u ku u_open
  exact measure_mono (hk.closure_subset_of_isOpen u_open ku)

/--
theorem `ext_isOpen` / 定理 `ext_isOpen`

English:
theorem ext_isOpen
  statement: {ν : Measure α} [OuterRegular μ] [OuterRegular ν]
  proof: by
  ext s ms
  rw [Set.measure_eq_iInf_isOpen]; rw [Set.measure_eq_iInf_isOpen]
  congr! 4 with t _ ht2
  exact hμν t ht2

中文:
定理 ext_isOpen
  结论: {ν : Measure α} [OuterRegular μ] [OuterRegular ν]
  证明: by
  ext s ms
  rw [Set.measure_eq_iInf_isOpen]; rw [Set.measure_eq_iInf_isOpen]
  congr! 4 with t _ ht2
  exact hμν t ht2

Depends on / 依赖: Set.measure_eq_iInf_isOpen, measure_eq_iInf_isOpen
-/
theorem ext_isOpen {ν : Measure α} [OuterRegular μ] [OuterRegular ν]
    (hμν : forall U, IsOpen U -> μ U = ν U) : μ = ν := by
  ext s ms
  rw [Set.measure_eq_iInf_isOpen]; rw [Set.measure_eq_iInf_isOpen]
  congr! 4 with t _ ht2
  exact hμν t ht2

/--
theorem `ext_isOpen_isBounded` / 定理 `ext_isOpen_isBounded`

English:
theorem ext_isOpen_isBounded
  statement: {α : Type*} [PseudoMetricSpace α] {mα : MeasurableSpace α}
  proof: by
  refine ext_isOpen fun U hU => ?_
  obtain ⟨f, hm, hu, hf⟩ := Metric.eq_countable_union_of_isBounded_of_isOpen hU
  rw [← hu]; rw [hm.measure_iUnion]; rw [hm.measure_iUnion]
  exact iSup_congr fun i => hμν (f i) (hf i).2 (hf i).1

中文:
定理 ext_isOpen_isBounded
  结论: {α : 类型} [PseudoMetricSpace α] {mα : MeasurableSpace α}
  证明: by
  refine ext_isOpen fun U hU => ?_
  obtain ⟨f, hm, hu, hf⟩ := Metric.eq_countable_union_of_isBounded_of_isOpen hU
  rw [← hu]; rw [hm.measure_iUnion]; rw [hm.measure_iUnion]
  exact iSup_congr fun i => hμν (f i) (hf i).2 (hf i).1

Depends on / 依赖: Metric, Metric.eq_countable_union_of_isBounded_of_isOpen, eq_countable_union_of_isBounded_of_isOpen, ext_isOpen, hm.measure_iUnion, iSup_congr, measure_iUnion
-/
theorem ext_isOpen_isBounded {α : Type*} [PseudoMetricSpace α] {mα : MeasurableSpace α}
    {μ ν : Measure α} [OuterRegular μ] [OuterRegular ν]
    (hμν : forall U, IsOpen U -> Bornology.IsBounded U -> μ U = ν U) : μ = ν := by
  refine ext_isOpen fun U hU => ?_
  obtain ⟨f, hm, hu, hf⟩ := Metric.eq_countable_union_of_isBounded_of_isOpen hU
  rw [← hu]; rw [hm.measure_iUnion]; rw [hm.measure_iUnion]
  exact iSup_congr fun i => hμν (f i) (hf i).2 (hf i).1

end OuterRegular

/--
theorem `FiniteSpanningSetsIn.outerRegular` / 定理 `FiniteSpanningSetsIn.outerRegular`

English:
theorem FiniteSpanningSetsIn.outerRegular
  proof: OuterRegular.of_restrict (s := fun n => s.set n) (fun n => (s.set_mem n).2)
    (fun n => (s.set_mem n).1) s.spanning.symm.subset

中文:
定理 FiniteSpanningSetsIn.outerRegular
  证明: OuterRegular.of_restrict (s := fun n => s.set n) (fun n => (s.set_mem n).2)
    (fun n => (s.set_mem n).1) s.spanning.symm.subset
-/
protected theorem FiniteSpanningSetsIn.outerRegular
    [TopologicalSpace α] [OpensMeasurableSpace α] {μ : Measure α}
    (s : μ.FiniteSpanningSetsIn { U | IsOpen U ∧ OuterRegular (μ.restrict U) }) :
    OuterRegular μ :=
  OuterRegular.of_restrict (s := fun n => s.set n) (fun n => (s.set_mem n).2)
    (fun n => (s.set_mem n).1) s.spanning.symm.subset

namespace InnerRegularWRT

variable {p : Set α -> Prop}

/--
lemma `of_restrict` / 引理 `of_restrict`

English:
lemma of_restrict
  statement: {μ : Measure α} {s : Nat -> Set α}
  proof: by
  intro F hF r hr
  have hBU : ⋃ n, F inter s n = F := by rw [← inter_iUnion, univ_subset_iff.mp hs, inter_univ]
  have : μ F = ⨆ n, μ (F inter s n) := by
    rw [← (monotone_const.inter hmono).measure_iUnion]; rw [hBU]
  rw [this] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  rw [← restrict_app

中文:
引理 of_restrict
  结论: {μ : Measure α} {s : 自然数 -> Set α}
  证明: by
  intro F hF r hr
  have hBU : ⋃ n, F inter s n = F := by rw [← inter_iUnion, univ_subset_iff.mp hs, inter_univ]
  have : μ F = ⨆ n, μ (F inter s n) := by
    rw [← (monotone_const.inter hmono).measure_iUnion]; rw [hBU]
  rw [this] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  rw [← restrict_app

Depends on / 依赖: hK.trans_le, inter_iUnion, inter_univ, lt_iSup_iff, measure_iUnion, monotone_const, monotone_const.inter, restrict_apply, restrict_apply_le, trans_le, univ_subset_iff, univ_subset_iff.mp
-/
lemma of_restrict {μ : Measure α} {s : Nat -> Set α}
    (h : forall n, InnerRegularWRT (μ.restrict (s n)) p MeasurableSet)
    (hs : univ subseteq ⋃ n, s n) (hmono : Monotone s) : InnerRegularWRT μ p MeasurableSet := by
  intro F hF r hr
  have hBU : ⋃ n, F inter s n = F := by rw [← inter_iUnion, univ_subset_iff.mp hs, inter_univ]
  have : μ F = ⨆ n, μ (F inter s n) := by
    rw [← (monotone_const.inter hmono).measure_iUnion]; rw [hBU]
  rw [this] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  rw [← restrict_apply hF] at hn
  rcases h n hF _ hn with ⟨K, KF, hKp, hK⟩
  exact ⟨K, KF, hKp, hK.trans_le (restrict_apply_le _ _)⟩

/--
lemma `restrict` / 引理 `restrict`

English:
lemma restrict
  given: (h : InnerRegularWRT μ p (fun s => MeasurableSet s ∧ μ s != ∞)) (A : Set α)
  proof: by
  rintro s ⟨s_meas, hs⟩ r hr
  rw [restrict_apply s_meas] at hs
  obtain ⟨K, K_subs, pK, rK⟩ : exists K, K subseteq (toMeasurable μ (s inter A)) inter s ∧ p K ∧ r < μ K := by
    have : r < μ ((toMeasurable μ (s inter A)) inter s) := by
      apply hr.trans_le
      rw [restrict_apply s_meas]
exa

中文:
引理 restrict
  条件: (h : InnerRegularWRT μ p (fun s => MeasurableSet s ∧ μ s != ∞)) (A : Set α)
  证明: by
  rintro s ⟨s_meas, hs⟩ r hr
  rw [restrict_apply s_meas] at hs
  obtain ⟨K, K_subs, pK, rK⟩ : exists K, K subseteq (toMeasurable μ (s inter A)) inter s ∧ p K ∧ r < μ K := by
    have : r < μ ((toMeasurable μ (s inter A)) inter s) := by
      apply hr.trans_le
      rw [restrict_apply s_meas]
exa

Depends on / 依赖: K_subs, hr.trans_le, hs.lt_top, inter_subset_left, lt_of_le_of_lt, lt_top, measurableSet_toMeasurable, measure_mono, measure_toMeasurable, restrict_apply, s_meas, subset_inter, subset_toMeasurable, subseteq, toMeasurable, trans_le
-/
lemma restrict (h : InnerRegularWRT μ p (fun s => MeasurableSet s ∧ μ s != ∞)) (A : Set α) :
    InnerRegularWRT (μ.restrict A) p (fun s => MeasurableSet s ∧ μ.restrict A s != ∞) := by
  rintro s ⟨s_meas, hs⟩ r hr
  rw [restrict_apply s_meas] at hs
  obtain ⟨K, K_subs, pK, rK⟩ : exists K, K subseteq (toMeasurable μ (s inter A)) inter s ∧ p K ∧ r < μ K := by
    have : r < μ ((toMeasurable μ (s inter A)) inter s) := by
      apply hr.trans_le
      rw [restrict_apply s_meas]
exact measure_mono subset_inter (subset_toMeasurable μ (s inter A)) inter_subset_left
    refine h ⟨(measurableSet_toMeasurable _ _).inter s_meas, ?_⟩ _ this
    apply (lt_of_le_of_lt _ hs.lt_top).ne
    rw [← measure_toMeasurable (s inter A)]
    exact measure_mono inter_subset_left
  refine ⟨K, K_subs.trans inter_subset_right, pK, ?_⟩
  calc
  r < μ K := rK
  _ = μ.restrict (toMeasurable μ (s inter A)) K := by
    rw [restrict_apply' (measurableSet_toMeasurable μ (s inter A))]
    congr
    apply (inter_eq_left.2 ?_).symm
    exact K_subs.trans inter_subset_left
  _ = μ.restrict (s inter A) K := by rwa [restrict_toMeasurable]
  _ <= μ.restrict A K := Measure.le_iff'.1 (restrict_mono inter_subset_right le_rfl) K

/--
lemma `restrict_of_measure_ne_top` / 引理 `restrict_of_measure_ne_top`

English:
lemma restrict_of_measure_ne_top
  statement: (h : InnerRegularWRT μ p (fun s => MeasurableSet s ∧ μ s != ∞))
  proof: by
  have : Fact (μ A < ∞) := ⟨hA.lt_top⟩
  exact (restrict h A).trans (of_imp (fun s hs => ⟨hs, measure_ne_top _ _⟩))

中文:
引理 restrict_of_measure_ne_top
  结论: (h : InnerRegularWRT μ p (fun s => MeasurableSet s ∧ μ s != ∞))
  证明: by
  have : Fact (μ A < ∞) := ⟨hA.lt_top⟩
  exact (restrict h A).trans (of_imp (fun s hs => ⟨hs, measure_ne_top _ _⟩))

Depends on / 依赖: hA.lt_top, lt_top, measure_ne_top, of_imp, restrict
-/
lemma restrict_of_measure_ne_top (h : InnerRegularWRT μ p (fun s => MeasurableSet s ∧ μ s != ∞))
    {A : Set α} (hA : μ A != ∞) :
    InnerRegularWRT (μ.restrict A) p (fun s => MeasurableSet s) := by
  have : Fact (μ A < ∞) := ⟨hA.lt_top⟩
  exact (restrict h A).trans (of_imp (fun s hs => ⟨hs, measure_ne_top _ _⟩))

/--
lemma `of_sigmaFinite` / 引理 `of_sigmaFinite`

English:
lemma of_sigmaFinite
  given: [SigmaFinite μ]
  proof: by
  intro s hs r hr
  set B : Nat -> Set α := spanningSets μ
  have hBU : ⋃ n, s inter B n = s := by rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
  have : μ s = ⨆ n, μ (s inter B n) := by
    rw [← (monotone_const.inter (monotone_spanningSets μ)).measure_iUnion]; rw [hBU]
  rw [this] at hr


中文:
引理 of_sigmaFinite
  条件: [SigmaFinite μ]
  证明: by
  intro s hs r hr
  set B : Nat -> Set α := spanningSets μ
  have hBU : ⋃ n, s inter B n = s := by rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
  have : μ s = ⨆ n, μ (s inter B n) := by
    rw [← (monotone_const.inter (monotone_spanningSets μ)).measure_iUnion]; rw [hBU]
  rw [this] at hr


Depends on / 依赖: hs.inter, iUnion_spanningSets, inter_iUnion, inter_subset_left, inter_subset_right, inter_univ, lt_iSup_iff, measurableSet_spanningSets, measure_iUnion, measure_mono, measure_spanningSets_lt_top, monotone_const, monotone_const.inter, monotone_spanningSets, spanningSets, trans_lt
-/
lemma of_sigmaFinite [SigmaFinite μ] :
    InnerRegularWRT μ (fun s => MeasurableSet s ∧ μ s != ∞) (fun s => MeasurableSet s) := by
  intro s hs r hr
  set B : Nat -> Set α := spanningSets μ
  have hBU : ⋃ n, s inter B n = s := by rw [← inter_iUnion, iUnion_spanningSets, inter_univ]
  have : μ s = ⨆ n, μ (s inter B n) := by
    rw [← (monotone_const.inter (monotone_spanningSets μ)).measure_iUnion]; rw [hBU]
  rw [this] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  refine ⟨s inter B n, inter_subset_left, ⟨hs.inter (measurableSet_spanningSets μ n), ?_⟩, hn⟩
  exact ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne

variable [TopologicalSpace α]

/--
theorem `measurableSet_of_isOpen` / 定理 `measurableSet_of_isOpen`

English:
theorem measurableSet_of_isOpen
  statement: [OuterRegular μ] (H : InnerRegularWRT μ p IsOpen)
  proof: by
  rintro s ⟨hs, hμs⟩ r hr
  have h0 : p ∅ := by
    have : 0 < μ univ := (bot_le.trans_lt hr).trans_le (measure_mono (subset_univ _))
    obtain ⟨K, -, hK, -⟩ : exists K, K subseteq univ ∧ p K ∧ 0 < μ K := H isOpen_univ _ this
    simpa using hd hK isOpen_univ
  obtain ⟨ε, hε, hεs, rfl⟩ : exists 

中文:
定理 measurableSet_of_isOpen
  结论: [OuterRegular μ] (H : InnerRegularWRT μ p IsOpen)
  证明: by
  rintro s ⟨hs, hμs⟩ r hr
  have h0 : p ∅ := by
    have : 0 < μ univ := (bot_le.trans_lt hr).trans_le (measure_mono (subset_univ _))
    obtain ⟨K, -, hK, -⟩ : exists K, K subseteq univ ∧ p K ∧ 0 < μ K := H isOpen_univ _ this
    simpa using hd hK isOpen_univ
  obtain ⟨ε, hε, hεs, rfl⟩ : exists 

Depends on / 依赖: ENNReal, ENNReal.add_halves, ENNReal.sub_sub_cancel, add_halves, bot_le, bot_le.trans_lt, exists_isOpen_sdiff_lt, hr.le, hs.exists_isOpen_sdiff_lt, isOpen_univ, measure_mono, sub_sub_cancel, subset_univ, subseteq, trans_le, trans_lt, tsub_eq_zero_iff_le
-/
theorem measurableSet_of_isOpen [OuterRegular μ] (H : InnerRegularWRT μ p IsOpen)
    (hd : forall ⦃s U⦄, p s -> IsOpen U -> p (s \ U)) :
    InnerRegularWRT μ p fun s => MeasurableSet s ∧ μ s != ∞ := by
  rintro s ⟨hs, hμs⟩ r hr
  have h0 : p ∅ := by
    have : 0 < μ univ := (bot_le.trans_lt hr).trans_le (measure_mono (subset_univ _))
    obtain ⟨K, -, hK, -⟩ : exists K, K subseteq univ ∧ p K ∧ 0 < μ K := H isOpen_univ _ this
    simpa using hd hK isOpen_univ
  obtain ⟨ε, hε, hεs, rfl⟩ : exists ε != 0, ε + ε <= μ s ∧ r = μ s - (ε + ε) := by
    use (μ s - r) / 2
    simp [*, hr.le, ENNReal.add_halves, ENNReal.sub_sub_cancel, tsub_eq_zero_iff_le]
  rcases hs.exists_isOpen_sdiff_lt hμs hε with ⟨U, hsU, hUo, hUt, hμU⟩
  rcases (U \ s).exists_isOpen_lt_of_lt _ hμU with ⟨U', hsU', hU'o, hμU'⟩
  replace hsU' := sdiff_subset_comm.1 hsU'
  rcases H.exists_subset_lt_add h0 hUo hUt.ne hε with ⟨K, hKU, hKc, hKr⟩
  refine ⟨K \ U', fun x hx => hsU' ⟨hKU hx.1, hx.2⟩, hd hKc hU'o, ENNReal.sub_lt_of_lt_add hεs ?_⟩
  calc
    μ s <= μ U := μ.mono hsU
    _ < μ K + ε := hKr
    _ <= μ (K \ U') + μ U' + ε := by grw [tsub_le_iff_right.1 le_measure_sdiff]
    _ <= μ (K \ U') + ε + ε := by gcongr
    _ = μ (K \ U') + (ε + ε) := add_assoc _ _ _

open Finset in
/--
theorem `weaklyRegular_of_finite` / 定理 `weaklyRegular_of_finite`

English:
theorem weaklyRegular_of_finite
  statement: [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  proof: by
  have hfin : forall {s}, μ s != ∞ := @(measure_ne_top μ)
  suffices forall s, MeasurableSet s -> forall ε, ε != 0 -> exists F, F subseteq s ∧ exists U, U ⊇ s ∧
      IsClosed F ∧ IsOpen U ∧ μ s <= μ F + ε ∧ μ U <= μ s + ε by
    refine
      { outerRegular := fun s hs r hr => ?_
        innerReg

中文:
定理 weaklyRegular_of_finite
  结论: [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  证明: by
  have hfin : forall {s}, μ s != ∞ := @(measure_ne_top μ)
  suffices forall s, MeasurableSet s -> forall ε, ε != 0 -> exists F, F subseteq s ∧ exists U, U ⊇ s ∧
      IsClosed F ∧ IsOpen U ∧ μ s <= μ F + ε ∧ μ U <= μ s + ε by
    refine
      { outerRegular := fun s hs r hr => ?_
        innerReg

Depends on / 依赖: H.trans_lt, IsClosed, IsOpen, MeasurableSet, add_tsub_cancel_of_le, exists_between, innerRegular, measure_ne_top, outerRegular, subseteq, trans_lt, tsub_pos_iff_lt
-/
theorem weaklyRegular_of_finite [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (H : InnerRegularWRT μ IsClosed IsOpen) : WeaklyRegular μ := by
  have hfin : forall {s}, μ s != ∞ := @(measure_ne_top μ)
  suffices forall s, MeasurableSet s -> forall ε, ε != 0 -> exists F, F subseteq s ∧ exists U, U ⊇ s ∧
      IsClosed F ∧ IsOpen U ∧ μ s <= μ F + ε ∧ μ U <= μ s + ε by
    refine
      { outerRegular := fun s hs r hr => ?_
        innerRegular := H }
    rcases exists_between hr with ⟨r', hsr', hr'r⟩
    rcases this s hs _ (tsub_pos_iff_lt.2 hsr').ne' with ⟨-, -, U, hsU, -, hUo, -, H⟩
    refine ⟨U, hsU, hUo, ?_⟩
    rw [add_tsub_cancel_of_le hsr'.le] at H
    exact H.trans_lt hr'r
  apply MeasurableSet.induction_on_open
  /- The proof is by measurable induction: we should check that the property is true for the empty
    set, for open sets, and is stable by taking the complement and by taking countable disjoint
    unions. The point of the property we are proving is that it is stable by taking complements
    (exchanging the roles of closed and open sets and thanks to the finiteness of the measure). -/
  -- check for open set
  · intro U hU ε hε
    rcases H.exists_subset_lt_add isClosed_empty hU hfin hε with ⟨F, hsF, hFc, hF⟩
    exact ⟨F, hsF, U, Subset.rfl, hFc, hU, hF.le, le_self_add⟩
  -- check for complements
  · rintro s hs H ε hε
    rcases H ε hε with ⟨F, hFs, U, hsU, hFc, hUo, hF, hU⟩
    refine
      ⟨Uᶜ, compl_subset_compl.2 hsU, Fᶜ, compl_subset_compl.2 hFs, hUo.isClosed_compl,
        hFc.isOpen_compl, ?_⟩
    simp only [measure_compl_le_add_iff, *, hUo.measurableSet, hFc.measurableSet, true_and]
  -- check for disjoint unions
  · intro s hsd hsm H ε ε0
    have ε0' : ε / 2 != 0 := (ENNReal.half_pos ε0).ne'
    rcases ENNReal.exists_pos_sum_of_countable' ε0' Nat with ⟨δ, δ0, hδε⟩
    choose F hFs U hsU hFc hUo hF hU using fun n => H n (δ n) (δ0 n).ne'
    -- the approximating closed set is constructed by considering finitely many sets `s i`, which
    -- cover all the measure up to `ε/2`, approximating each of these by a closed set `F i`, and
    -- taking the union of these (finitely many) `F i`.
    have : Tendsto (fun t => (∑ k in t, μ (s k)) + ε / 2) atTop (𝓝 <| μ (⋃ n, s n) + ε / 2) := by
      rw [measure_iUnion hsd hsm]
      exact Tendsto.add ENNReal.summable.hasSum tendsto_const_nhds
    rcases (this.eventually <| lt_mem_nhds <| ENNReal.lt_add_right hfin ε0').exists with ⟨t, ht⟩
    -- the approximating open set is constructed by taking for each `s n` an approximating open set
    -- `U n` with measure at most `μ (s n) + δ n` for a summable `δ`, and taking the union of these.
    refine
      ⟨⋃ k in t, F k, iUnion_mono fun k => iUnion_subset fun _ => hFs _, ⋃ n, U n, iUnion_mono hsU,
        isClosed_biUnion_finset fun k _ => hFc k, isOpen_iUnion hUo, ht.le.trans ?_, ?_⟩
    · calc
        (∑ k in t, μ (s k)) + ε / 2 <= ((∑ k in t, μ (F k)) + ∑ k in t, δ k) + ε / 2 := by
          rw [← sum_add_distrib]
          gcongr
          apply hF
        _ <= (∑ k in t, μ (F k)) + ε / 2 + ε / 2 := by
          gcongr
          exact (ENNReal.sum_le_tsum _).trans hδε.le
        _ = μ (⋃ k in t, F k) + ε := by
          rw [measure_biUnion_finset]; rw [add_assoc]; rw [ENNReal.add_halves]
          exacts [fun k _ n _ hkn => (hsd hkn).mono (hFs k) (hFs n),
            fun k _ => (hFc k).measurableSet]
    · calc
        μ (⋃ n, U n) <= ∑' n, μ (U n) := measure_iUnion_le _
        _ <= ∑' n, (μ (s n) + δ n) := ENNReal.tsum_le_tsum hU
        _ = μ (⋃ n, s n) + ∑' n, δ n := by rw [measure_iUnion hsd hsm, ENNReal.tsum_add]
        _ <= μ (⋃ n, s n) + ε := by grw [hδε, ENNReal.half_le_self]

/--
theorem `of_pseudoMetrizableSpace` / 定理 `of_pseudoMetrizableSpace`

English:
theorem of_pseudoMetrizableSpace
  statement: {X : Type*} [TopologicalSpace X] [PseudoMetrizableSpace X]
  proof: by
  let A : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  intro U hU r hr
  rcases hU.exists_iUnion_isClosed with ⟨F, F_closed, -, rfl, F_mono⟩
  rw [F_mono.measure_iUnion] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  exact ⟨F n, subset_iUnion _ _, F_closed n, hn⟩

中文:
定理 of_pseudoMetrizableSpace
  结论: {X : 类型} [TopologicalSpace X] [PseudoMetrizableSpace X]
  证明: by
  let A : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  intro U hU r hr
  rcases hU.exists_iUnion_isClosed with ⟨F, F_closed, -, rfl, F_mono⟩
  rw [F_mono.measure_iUnion] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  exact ⟨F n, subset_iUnion _ _, F_closed n, hn⟩

Depends on / 依赖: F_closed, F_mono, F_mono.measure_iUnion, PseudoMetricSpace, TopologicalSpace, TopologicalSpace.pseudoMetrizableSpacePseudoMetric, exists_iUnion_isClosed, hU.exists_iUnion_isClosed, lt_iSup_iff, measure_iUnion, pseudoMetrizableSpacePseudoMetric, subset_iUnion
-/
theorem of_pseudoMetrizableSpace {X : Type*} [TopologicalSpace X] [PseudoMetrizableSpace X]
    [MeasurableSpace X] (μ : Measure X) : InnerRegularWRT μ IsClosed IsOpen := by
  let A : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  intro U hU r hr
  rcases hU.exists_iUnion_isClosed with ⟨F, F_closed, -, rfl, F_mono⟩
  rw [F_mono.measure_iUnion] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  exact ⟨F n, subset_iUnion _ _, F_closed n, hn⟩

/--
theorem `isCompact_isClosed` / 定理 `isCompact_isClosed`

English:
theorem isCompact_isClosed
  statement: {X : Type*} [TopologicalSpace X] [SigmaCompactSpace X]
  proof: by
  intro F hF r hr
  set B : Nat -> Set X := compactCovering X
  have hBc : forall n, IsCompact (F inter B n) := fun n => (isCompact_compactCovering X n).inter_left hF
  have hBU : ⋃ n, F inter B n = F := by rw [← inter_iUnion, iUnion_compactCovering, Set.inter_univ]
  have : μ F = ⨆ n, μ (F inter

中文:
定理 isCompact_isClosed
  结论: {X : 类型} [TopologicalSpace X] [SigmaCompactSpace X]
  证明: by
  intro F hF r hr
  set B : Nat -> Set X := compactCovering X
  have hBc : forall n, IsCompact (F inter B n) := fun n => (isCompact_compactCovering X n).inter_left hF
  have hBU : ⋃ n, F inter B n = F := by rw [← inter_iUnion, iUnion_compactCovering, Set.inter_univ]
  have : μ F = ⨆ n, μ (F inter

Depends on / 依赖: IsCompact, Monotone, Monotone.measure_iUnion, Set.inter_univ, compactCovering, iUnion_compactCovering, inter_iUnion, inter_left, inter_subset_left, inter_univ, isCompact_compactCovering, lt_iSup_iff, measure_iUnion, monotone_accumulate, monotone_const, monotone_const.inter
-/
theorem isCompact_isClosed {X : Type*} [TopologicalSpace X] [SigmaCompactSpace X]
    [MeasurableSpace X] (μ : Measure X) : InnerRegularWRT μ IsCompact IsClosed := by
  intro F hF r hr
  set B : Nat -> Set X := compactCovering X
  have hBc : forall n, IsCompact (F inter B n) := fun n => (isCompact_compactCovering X n).inter_left hF
  have hBU : ⋃ n, F inter B n = F := by rw [← inter_iUnion, iUnion_compactCovering, Set.inter_univ]
  have : μ F = ⨆ n, μ (F inter B n) := by
    rw [← Monotone.measure_iUnion]; rw [hBU]
    exact monotone_const.inter monotone_accumulate
  rw [this] at hr
  rcases lt_iSup_iff.1 hr with ⟨n, hn⟩
  exact ⟨_, inter_subset_left, hBc n, hn⟩

end InnerRegularWRT

namespace InnerRegular

variable [TopologicalSpace α]

/--
theorem `_root_.MeasurableSet.measure_eq_iSup_isCompact` / 定理 `_root_.MeasurableSet.measure_eq_iSup_isCompact`

English:
theorem _root_.MeasurableSet.measure_eq_iSup_isCompact
  given: ⦃U
  statement: Set α⦄ (hU : MeasurableSet U)
  proof: InnerRegular.innerRegular.measure_eq_iSup hU

中文:
定理 _root_.MeasurableSet.measure_eq_iSup_isCompact
  条件: ⦃U
  结论: Set α⦄ (hU : MeasurableSet U)
  证明: InnerRegular.innerRegular.measure_eq_iSup hU

Depends on / 依赖: InnerRegular, InnerRegular.innerRegular.measure_eq_iSup, innerRegular, measure_eq_iSup
-/
theorem _root_.MeasurableSet.measure_eq_iSup_isCompact ⦃U : Set α⦄ (hU : MeasurableSet U)
    (μ : Measure α) [InnerRegular μ] :
    μ U = ⨆ (K : Set α) (_ : K subseteq U) (_ : IsCompact K), μ K :=
  InnerRegular.innerRegular.measure_eq_iSup hU

/--
Instance `zero` / 实例 `zero`

English:
instance zero
  signature: : InnerRegular (0 : Measure α)
  body: ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isCompact_empty, hr⟩⟩

中文:
实例 zero
  签名: : InnerRegular (0 : Measure α)
  定义体: ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isCompact_empty, hr⟩⟩

Depends on / 依赖: empty_subset, isCompact_empty
-/
instance zero : InnerRegular (0 : Measure α) :=
  ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isCompact_empty, hr⟩⟩

/--
Instance `smul` / 实例 `smul`

English:
instance smul
  signature: [h : InnerRegular μ] (c : Real>=0∞)
  body: ⟨InnerRegularWRT.smul h.innerRegular c⟩

中文:
实例 smul
  签名: [h : InnerRegular μ] (c : 实数>=0∞)
  定义体: ⟨InnerRegularWRT.smul h.innerRegular c⟩

Depends on / 依赖: InnerRegularWRT, InnerRegularWRT.smul, h.innerRegular, innerRegular
-/
instance smul [h : InnerRegular μ] (c : Real>=0∞) : InnerRegular (c • μ) :=
  ⟨InnerRegularWRT.smul h.innerRegular c⟩

/--
Instance `smul_nnreal` / 实例 `smul_nnreal`

English:
instance smul_nnreal
  signature: [InnerRegular μ] (c : Real>=0)
  body: smul (c : Real>=0∞)

中文:
实例 smul_nnreal
  签名: [InnerRegular μ] (c : 实数>=0)
  定义体: smul (c : Real>=0∞)
-/
instance smul_nnreal [InnerRegular μ] (c : Real>=0) : InnerRegular (c • μ) := smul (c : Real>=0∞)

instance (priority := 100) [InnerRegular μ] : InnerRegularCompactLTTop μ :=
  ⟨fun _s hs r hr => InnerRegular.innerRegular hs.1 r hr⟩

/--
lemma `innerRegularWRT_isClosed_isOpen` / 引理 `innerRegularWRT_isClosed_isOpen`

English:
lemma innerRegularWRT_isClosed_isOpen
  given: [R1Space α] [OpensMeasurableSpace α] [h : InnerRegular μ]
  proof: by
  intro U hU r hr
  rcases h.innerRegular hU.measurableSet r hr with ⟨K, KU, K_comp, hK⟩
  exact ⟨closure K, K_comp.closure_subset_of_isOpen hU KU, isClosed_closure,
    hK.trans_le (measure_mono subset_closure)⟩

中文:
引理 innerRegularWRT_isClosed_isOpen
  条件: [R1Space α] [OpensMeasurableSpace α] [h : InnerRegular μ]
  证明: by
  intro U hU r hr
  rcases h.innerRegular hU.measurableSet r hr with ⟨K, KU, K_comp, hK⟩
  exact ⟨closure K, K_comp.closure_subset_of_isOpen hU KU, isClosed_closure,
    hK.trans_le (measure_mono subset_closure)⟩

Depends on / 依赖: K_comp, K_comp.closure_subset_of_isOpen, closure, closure_subset_of_isOpen, h.innerRegular, hK.trans_le, hU.measurableSet, innerRegular, isClosed_closure, measurableSet, measure_mono, subset_closure, trans_le
-/
lemma innerRegularWRT_isClosed_isOpen [R1Space α] [OpensMeasurableSpace α] [h : InnerRegular μ] :
    InnerRegularWRT μ IsClosed IsOpen := by
  intro U hU r hr
  rcases h.innerRegular hU.measurableSet r hr with ⟨K, KU, K_comp, hK⟩
  exact ⟨closure K, K_comp.closure_subset_of_isOpen hU KU, isClosed_closure,
    hK.trans_le (measure_mono subset_closure)⟩

/--
theorem `exists_isCompact_not_null` / 定理 `exists_isCompact_not_null`

English:
theorem exists_isCompact_not_null
  given: [InnerRegular μ]
  statement: (exists K, IsCompact K ∧ μ K != 0) ↔ μ != 0
  proof: by
  simp_rw [Ne, ← measure_univ_eq_zero, MeasurableSet.univ.measure_eq_iSup_isCompact,
    ENNReal.iSup_eq_zero, not_forall, exists_prop, subset_univ, true_and]

中文:
定理 exists_isCompact_not_null
  条件: [InnerRegular μ]
  结论: (存在 K, IsCompact K ∧ μ K != 0) ↔ μ != 0
  证明: by
  simp_rw [Ne, ← measure_univ_eq_zero, MeasurableSet.univ.measure_eq_iSup_isCompact,
    ENNReal.iSup_eq_zero, not_forall, exists_prop, subset_univ, true_and]

Depends on / 依赖: ENNReal, ENNReal.iSup_eq_zero, MeasurableSet, MeasurableSet.univ.measure_eq_iSup_isCompact, exists_prop, iSup_eq_zero, measure_eq_iSup_isCompact, measure_univ_eq_zero, not_forall, simp_rw, subset_univ, true_and
-/
theorem exists_isCompact_not_null [InnerRegular μ] : (exists K, IsCompact K ∧ μ K != 0) ↔ μ != 0 := by
  simp_rw [Ne, ← measure_univ_eq_zero, MeasurableSet.univ.measure_eq_iSup_isCompact,
    ENNReal.iSup_eq_zero, not_forall, exists_prop, subset_univ, true_and]
/--
theorem `_root_.MeasurableSet.exists_lt_isCompact` / 定理 `_root_.MeasurableSet.exists_lt_isCompact`

English:
theorem _root_.MeasurableSet.exists_lt_isCompact
  given: [InnerRegular μ] ⦃A
  statement: Set α⦄
  proof: InnerRegular.innerRegular hA _ hr

中文:
定理 _root_.MeasurableSet.exists_lt_isCompact
  条件: [InnerRegular μ] ⦃A
  结论: Set α⦄
  证明: InnerRegular.innerRegular hA _ hr

Depends on / 依赖: InnerRegular, InnerRegular.innerRegular, innerRegular
-/
theorem _root_.MeasurableSet.exists_lt_isCompact [InnerRegular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) {r : Real>=0∞} (hr : r < μ A) :
    exists K, K subseteq A ∧ IsCompact K ∧ r < μ K :=
  InnerRegular.innerRegular hA _ hr

/--
theorem `map_of_continuous` / 定理 `map_of_continuous`

English:
theorem map_of_continuous
  statement: [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
  proof: ⟨InnerRegularWRT.map h.innerRegular hf.aemeasurable (fun _s hs => hf.measurable hs)
    (fun _K hK => hK.image hf) (fun _s hs => hs)⟩

中文:
定理 map_of_continuous
  结论: [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
  证明: ⟨InnerRegularWRT.map h.innerRegular hf.aemeasurable (fun _s hs => hf.measurable hs)
    (fun _K hK => hK.image hf) (fun _s hs => hs)⟩
-/
protected theorem map_of_continuous [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] [h : InnerRegular μ] {f : α -> β} (hf : Continuous f) :
    InnerRegular (Measure.map f μ) :=
  ⟨InnerRegularWRT.map h.innerRegular hf.aemeasurable (fun _s hs => hf.measurable hs)
    (fun _K hK => hK.image hf) (fun _s hs => hs)⟩

/--
theorem `map` / 定理 `map`

English:
theorem map
  statement: [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
  proof: InnerRegular.map_of_continuous f.continuous

中文:
定理 map
  结论: [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
  证明: InnerRegular.map_of_continuous f.continuous
-/
protected theorem map [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] [InnerRegular μ] (f : α ≃ₜ β) : (Measure.map f μ).InnerRegular :=
  InnerRegular.map_of_continuous f.continuous

/--
theorem `map_iff` / 定理 `map_iff`

English:
theorem map_iff
  statement: [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
  proof: by
  refine ⟨fun h => ?_, fun h => h.map f⟩
  convert! h.map f.symm
  rw [map_map f.symm.continuous.measurable f.continuous.measurable]
  simp

中文:
定理 map_iff
  结论: [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
  证明: by
  refine ⟨fun h => ?_, fun h => h.map f⟩
  convert! h.map f.symm
  rw [map_map f.symm.continuous.measurable f.continuous.measurable]
  simp
-/
protected theorem map_iff [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] (f : α ≃ₜ β) :
    InnerRegular (Measure.map f μ) ↔ InnerRegular μ := by
  refine ⟨fun h => ?_, fun h => h.map f⟩
  convert! h.map f.symm
  rw [map_map f.symm.continuous.measurable f.continuous.measurable]
  simp

open Topology in
/--
theorem `comap'` / 定理 `comap'`

English:
theorem comap'
  statement: [BorelSpace α]
  proof: H.innerRegular.comap hf.measurableEmbedding
    (fun _ hU => hf.measurableEmbedding.measurableSet_image' hU)
    (fun _ hKrange hK => hf.isInducing.isCompact_preimage' hK hKrange)

中文:
定理 comap'
  结论: [BorelSpace α]
  证明: H.innerRegular.comap hf.measurableEmbedding
    (fun _ hU => hf.measurableEmbedding.measurableSet_image' hU)
    (fun _ hKrange hK => hf.isInducing.isCompact_preimage' hK hKrange)
-/
protected theorem comap' [BorelSpace α]
    {mβ : MeasurableSpace β} [TopologicalSpace β] [BorelSpace β]
    (μ : Measure β) [H : InnerRegular μ] {f : α -> β} (hf : IsOpenEmbedding f) :
    (μ.comap f).InnerRegular where
  innerRegular :=
    H.innerRegular.comap hf.measurableEmbedding
    (fun _ hU => hf.measurableEmbedding.measurableSet_image' hU)
    (fun _ hKrange hK => hf.isInducing.isCompact_preimage' hK hKrange)

/--
theorem `comap` / 定理 `comap`

English:
theorem comap
  statement: [BorelSpace α] {mβ : MeasurableSpace β} [TopologicalSpace β] [BorelSpace β]
  proof: InnerRegular.comap' μ f.isOpenEmbedding

中文:
定理 comap
  结论: [BorelSpace α] {mβ : MeasurableSpace β} [TopologicalSpace β] [BorelSpace β]
  证明: InnerRegular.comap' μ f.isOpenEmbedding

Depends on / 依赖: X.toDistLat.str, toDistLat
-/
protected theorem comap [BorelSpace α] {mβ : MeasurableSpace β} [TopologicalSpace β] [BorelSpace β]
    {μ : Measure β} [InnerRegular μ] (f : α ≃ₜ β) :
    (μ.comap f).InnerRegular :=
  InnerRegular.comap' μ f.isOpenEmbedding

instance {μ ν : Measure α} [InnerRegular μ] [InnerRegular ν] : InnerRegular (μ + ν) := by
  constructor
  intro s hs r hr
  simp only [Measure.coe_add, Pi.add_apply] at hr
  rcases eq_or_ne (μ s) 0 with h | h
  · simp only [h, zero_add] at hr
    rcases MeasurableSet.exists_lt_isCompact hs hr with ⟨K, Ks, hK, h'K⟩
    exact ⟨K, Ks, hK, h'K.trans_le (by simp)⟩
  rcases eq_or_ne (ν s) 0 with h' | h'
  · simp only [h', add_zero] at hr
    rcases MeasurableSet.exists_lt_isCompact hs hr with ⟨K, Ks, hK, h'K⟩
    exact ⟨K, Ks, hK, h'K.trans_le (by simp)⟩
  rcases ENNReal.exists_lt_add_of_lt_add hr h h' with ⟨u, hu, v, hv, huv⟩
  rcases MeasurableSet.exists_lt_isCompact hs hu with ⟨K, Ks, hK, h'K⟩
  rcases MeasurableSet.exists_lt_isCompact hs hv with ⟨K', K's, hK', h'K'⟩
  refine ⟨K union K', union_subset Ks K's, hK.union hK', huv.trans_le ?_⟩
  apply (add_le_add h'K.le h'K'.le).trans
  simp only [Measure.coe_add, Pi.add_apply]
  gcongr <;> simp

instance {ι : Type*} {μ : ι -> Measure α} [forall i, InnerRegular (μ i)] (a : Finset ι) :
    InnerRegular (∑ i in a, μ i) := by
  classical
  induction a using Finset.induction with
  | empty => simp only [Finset.sum_empty]; infer_instance
  | insert a s ha ih => simp only [ha, not_false_eq_true, Finset.sum_insert]; infer_instance

instance {ι : Type*} {μ : ι -> Measure α} [forall i, InnerRegular (μ i)] :
    InnerRegular (Measure.sum μ) := by
  constructor
  intro s hs r hr
  have : Tendsto (fun (a : Finset ι) => ∑ i in a, μ i s) atTop (𝓝 (Measure.sum μ s)) := by
    simp only [hs, Measure.sum_apply]
    exact ENNReal.summable.hasSum
  obtain ⟨a, ha⟩ : exists (a : Finset ι), r < (∑ i in a, μ i) s := by
    simp only [coe_finsetSum, Finset.sum_apply]
    exact ((tendsto_order.1 this).1 r hr).exists
  rcases MeasurableSet.exists_lt_isCompact hs ha with ⟨K, Ks, hK, h'K⟩
  refine ⟨K, Ks, hK, h'K.trans_le ?_⟩
  simp only [coe_finsetSum, Finset.sum_apply]
  exact (ENNReal.sum_le_tsum _).trans (le_sum_apply _ _)

end InnerRegular

namespace InnerRegularCompactLTTop

variable [TopologicalSpace α]

/--
theorem `_root_.MeasurableSet.exists_isCompact_lt_add` / 定理 `_root_.MeasurableSet.exists_isCompact_lt_add`

English:
theorem _root_.MeasurableSet.exists_isCompact_lt_add
  statement: [InnerRegularCompactLTTop μ]
  proof: InnerRegularCompactLTTop.innerRegular.exists_subset_lt_add isCompact_empty ⟨hA, h'A⟩ h'A hε

中文:
定理 _root_.MeasurableSet.exists_isCompact_lt_add
  结论: [InnerRegularCompactLTTop μ]
  证明: InnerRegularCompactLTTop.innerRegular.exists_subset_lt_add isCompact_empty ⟨hA, h'A⟩ h'A hε

Depends on / 依赖: InnerRegularCompactLTTop, InnerRegularCompactLTTop.innerRegular.exists_subset_lt_add, exists_subset_lt_add, innerRegular, isCompact_empty
-/
theorem _root_.MeasurableSet.exists_isCompact_lt_add [InnerRegularCompactLTTop μ]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A != ∞) {ε : Real>=0∞} (hε : ε != 0) :
    exists K, K subseteq A ∧ IsCompact K ∧ μ A < μ K + ε :=
  InnerRegularCompactLTTop.innerRegular.exists_subset_lt_add isCompact_empty ⟨hA, h'A⟩ h'A hε

/--
theorem `_root_.MeasurableSet.exists_isCompact_isClosed_lt_add` / 定理 `_root_.MeasurableSet.exists_isCompact_isClosed_lt_add`

English:
theorem _root_.MeasurableSet.exists_isCompact_isClosed_lt_add
  proof: let ⟨K, hKA, hK, hμK⟩ := hA.exists_isCompact_lt_add h'A hε
  ⟨closure K, hK.closure_subset_measurableSet hA hKA, hK.closure, isClosed_closure,
    by rwa [hK.measure_closure]⟩

中文:
定理 _root_.MeasurableSet.exists_isCompact_isClosed_lt_add
  证明: let ⟨K, hKA, hK, hμK⟩ := hA.exists_isCompact_lt_add h'A hε
  ⟨closure K, hK.closure_subset_measurableSet hA hKA, hK.closure, isClosed_closure,
    by rwa [hK.measure_closure]⟩

Depends on / 依赖: closure, closure_subset_measurableSet, exists_isCompact_lt_add, hA.exists_isCompact_lt_add, hK.closure, hK.closure_subset_measurableSet, hK.measure_closure, isClosed_closure, measure_closure
-/
theorem _root_.MeasurableSet.exists_isCompact_isClosed_lt_add
    [InnerRegularCompactLTTop μ] [R1Space α] [BorelSpace α]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A != ∞) {ε : Real>=0∞} (hε : ε != 0) :
    exists K, K subseteq A ∧ IsCompact K ∧ IsClosed K ∧ μ A < μ K + ε :=
  let ⟨K, hKA, hK, hμK⟩ := hA.exists_isCompact_lt_add h'A hε
  ⟨closure K, hK.closure_subset_measurableSet hA hKA, hK.closure, isClosed_closure,
    by rwa [hK.measure_closure]⟩

/--
theorem `_root_.MeasurableSet.exists_isCompact_sdiff_lt` / 定理 `_root_.MeasurableSet.exists_isCompact_sdiff_lt`

English:
theorem _root_.MeasurableSet.exists_isCompact_sdiff_lt
  statement: [OpensMeasurableSpace α] [T2Space α]
  proof: by
  rcases hA.exists_isCompact_lt_add h'A hε with ⟨K, hKA, hKc, hK⟩
  exact ⟨K, hKA, hKc, measure_sdiff_lt_of_lt_add hKc.nullMeasurableSet hKA
    (ne_top_of_le_ne_top h'A <| measure_mono hKA) hK⟩

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isCompact_diff_lt :=
  _root_

中文:
定理 _root_.MeasurableSet.exists_isCompact_sdiff_lt
  结论: [OpensMeasurableSpace α] [T2Space α]
  证明: by
  rcases hA.exists_isCompact_lt_add h'A hε with ⟨K, hKA, hKc, hK⟩
  exact ⟨K, hKA, hKc, measure_sdiff_lt_of_lt_add hKc.nullMeasurableSet hKA
    (ne_top_of_le_ne_top h'A <| measure_mono hKA) hK⟩

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isCompact_diff_lt :=
  _root_

Depends on / 依赖: exists_isCompact_lt_add, hA.exists_isCompact_lt_add, hKc.nullMeasurableSet, measure_mono, measure_sdiff_lt_of_lt_add, ne_top_of_le_ne_top, nullMeasurableSet
-/
theorem _root_.MeasurableSet.exists_isCompact_sdiff_lt [OpensMeasurableSpace α] [T2Space α]
    [InnerRegularCompactLTTop μ] ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A != ∞)
    {ε : Real>=0∞} (hε : ε != 0) :
    exists K, K subseteq A ∧ IsCompact K ∧ μ (A \ K) < ε := by
  rcases hA.exists_isCompact_lt_add h'A hε with ⟨K, hKA, hKc, hK⟩
  exact ⟨K, hKA, hKc, measure_sdiff_lt_of_lt_add hKc.nullMeasurableSet hKA
    (ne_top_of_le_ne_top h'A <| measure_mono hKA) hK⟩

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isCompact_diff_lt :=
  _root_.MeasurableSet.exists_isCompact_sdiff_lt

/--
theorem `_root_.MeasurableSet.exists_isCompact_isClosed_sdiff_lt` / 定理 `_root_.MeasurableSet.exists_isCompact_isClosed_sdiff_lt`

English:
theorem _root_.MeasurableSet.exists_isCompact_isClosed_sdiff_lt
  statement: [BorelSpace α] [R1Space α]
  proof: by
  rcases hA.exists_isCompact_isClosed_lt_add h'A hε with ⟨K, hKA, hKco, hKcl, hK⟩
  exact ⟨K, hKA, hKco, hKcl, measure_sdiff_lt_of_lt_add hKcl.nullMeasurableSet hKA
    (ne_top_of_le_ne_top h'A <| measure_mono hKA) hK⟩

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isCom

中文:
定理 _root_.MeasurableSet.exists_isCompact_isClosed_sdiff_lt
  结论: [BorelSpace α] [R1Space α]
  证明: by
  rcases hA.exists_isCompact_isClosed_lt_add h'A hε with ⟨K, hKA, hKco, hKcl, hK⟩
  exact ⟨K, hKA, hKco, hKcl, measure_sdiff_lt_of_lt_add hKcl.nullMeasurableSet hKA
    (ne_top_of_le_ne_top h'A <| measure_mono hKA) hK⟩

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isCom

Depends on / 依赖: exists_isCompact_isClosed_lt_add, hA.exists_isCompact_isClosed_lt_add, hKcl.nullMeasurableSet, measure_mono, measure_sdiff_lt_of_lt_add, ne_top_of_le_ne_top, nullMeasurableSet
-/
theorem _root_.MeasurableSet.exists_isCompact_isClosed_sdiff_lt [BorelSpace α] [R1Space α]
    [InnerRegularCompactLTTop μ] ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A != ∞)
    {ε : Real>=0∞} (hε : ε != 0) :
    exists K, K subseteq A ∧ IsCompact K ∧ IsClosed K ∧ μ (A \ K) < ε := by
  rcases hA.exists_isCompact_isClosed_lt_add h'A hε with ⟨K, hKA, hKco, hKcl, hK⟩
  exact ⟨K, hKA, hKco, hKcl, measure_sdiff_lt_of_lt_add hKcl.nullMeasurableSet hKA
    (ne_top_of_le_ne_top h'A <| measure_mono hKA) hK⟩

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isCompact_isClosed_diff_lt :=
  _root_.MeasurableSet.exists_isCompact_isClosed_sdiff_lt

/--
theorem `_root_.MeasurableSet.exists_lt_isCompact_of_ne_top` / 定理 `_root_.MeasurableSet.exists_lt_isCompact_of_ne_top`

English:
theorem _root_.MeasurableSet.exists_lt_isCompact_of_ne_top
  given: [InnerRegularCompactLTTop μ] ⦃A
  statement: Set α⦄
  proof: InnerRegularCompactLTTop.innerRegular ⟨hA, h'A⟩ _ hr

中文:
定理 _root_.MeasurableSet.exists_lt_isCompact_of_ne_top
  条件: [InnerRegularCompactLTTop μ] ⦃A
  结论: Set α⦄
  证明: InnerRegularCompactLTTop.innerRegular ⟨hA, h'A⟩ _ hr

Depends on / 依赖: BddDistLat, ConcreteCategory, ConcreteCategory.hom, InnerRegularCompactLTTop, InnerRegularCompactLTTop.innerRegular, innerRegular
-/
theorem _root_.MeasurableSet.exists_lt_isCompact_of_ne_top [InnerRegularCompactLTTop μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A != ∞) {r : Real>=0∞} (hr : r < μ A) :
    exists K, K subseteq A ∧ IsCompact K ∧ r < μ K :=
  InnerRegularCompactLTTop.innerRegular ⟨hA, h'A⟩ _ hr

/--
theorem `_root_.MeasurableSet.measure_eq_iSup_isCompact_of_ne_top` / 定理 `_root_.MeasurableSet.measure_eq_iSup_isCompact_of_ne_top`

English:
theorem _root_.MeasurableSet.measure_eq_iSup_isCompact_of_ne_top
  statement: [InnerRegularCompactLTTop μ]
  proof: InnerRegularCompactLTTop.innerRegular.measure_eq_iSup ⟨hA, h'A⟩

中文:
定理 _root_.MeasurableSet.measure_eq_iSup_isCompact_of_ne_top
  结论: [InnerRegularCompactLTTop μ]
  证明: InnerRegularCompactLTTop.innerRegular.measure_eq_iSup ⟨hA, h'A⟩

Depends on / 依赖: InnerRegularCompactLTTop, InnerRegularCompactLTTop.innerRegular.measure_eq_iSup, innerRegular, measure_eq_iSup
-/
theorem _root_.MeasurableSet.measure_eq_iSup_isCompact_of_ne_top [InnerRegularCompactLTTop μ]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A != ∞) :
    μ A = ⨆ (K) (_ : K subseteq A) (_ : IsCompact K), μ K :=
  InnerRegularCompactLTTop.innerRegular.measure_eq_iSup ⟨hA, h'A⟩

/--
Instance `restrict` / 实例 `restrict`

English:
instance restrict
  signature: [h : InnerRegularCompactLTTop μ] (A : Set α)
  body: ⟨InnerRegularWRT.restrict h.innerRegular A⟩

中文:
实例 restrict
  签名: [h : InnerRegularCompactLTTop μ] (A : Set α)
  定义体: ⟨InnerRegularWRT.restrict h.innerRegular A⟩

Depends on / 依赖: InnerRegularWRT, InnerRegularWRT.restrict, f.hom, h.innerRegular, innerRegular, restrict
-/
instance restrict [h : InnerRegularCompactLTTop μ] (A : Set α) :
    InnerRegularCompactLTTop (μ.restrict A) :=
  ⟨InnerRegularWRT.restrict h.innerRegular A⟩

instance (priority := 50) [h : InnerRegularCompactLTTop μ] [IsFiniteMeasure μ] :
    InnerRegular μ := by
  constructor
  convert! h.innerRegular with s
  simp [measure_ne_top μ s]

instance (priority := 50) [BorelSpace α] [R1Space α] [InnerRegularCompactLTTop μ]
    [IsFiniteMeasure μ] : WeaklyRegular μ :=
  InnerRegular.innerRegularWRT_isClosed_isOpen.weaklyRegular_of_finite _

instance (priority := 50) [BorelSpace α] [R1Space α] [h : InnerRegularCompactLTTop μ]
    [IsFiniteMeasure μ] : Regular μ where
innerRegular := InnerRegularWRT.trans h.innerRegular
    InnerRegularWRT.of_imp (fun U hU => ⟨hU.measurableSet, measure_ne_top μ U⟩)

/--
lemma `_root_.IsCompact.exists_isOpen_lt_of_lt` / 引理 `_root_.IsCompact.exists_isOpen_lt_of_lt`

English:
lemma _root_.IsCompact.exists_isOpen_lt_of_lt
  statement: [InnerRegularCompactLTTop μ]
  proof: by
  rcases hK.exists_open_superset_measure_lt_top μ with ⟨V, hKV, hVo, hμV⟩
  have := Fact.mk hμV
  obtain ⟨U, hKU, hUo, hμU⟩ : exists U, K subseteq U ∧ IsOpen U ∧ μ.restrict V U < r :=
exists_isOpen_lt_of_lt K r (restrict_apply_le _ _).trans_lt hr
  refine ⟨U inter V, subset_inter hKU hKV, hUo.int

中文:
引理 _root_.IsCompact.exists_isOpen_lt_of_lt
  结论: [InnerRegularCompactLTTop μ]
  证明: by
  rcases hK.exists_open_superset_measure_lt_top μ with ⟨V, hKV, hVo, hμV⟩
  have := Fact.mk hμV
  obtain ⟨U, hKU, hUo, hμU⟩ : exists U, K subseteq U ∧ IsOpen U ∧ μ.restrict V U < r :=
exists_isOpen_lt_of_lt K r (restrict_apply_le _ _).trans_lt hr
  refine ⟨U inter V, subset_inter hKU hKV, hUo.int
-/
protected lemma _root_.IsCompact.exists_isOpen_lt_of_lt [InnerRegularCompactLTTop μ]
    [IsLocallyFiniteMeasure μ] [R1Space α] [BorelSpace α] {K : Set α}
    (hK : IsCompact K) (r : Real>=0∞) (hr : μ K < r) :
    exists U, K subseteq U ∧ IsOpen U ∧ μ U < r := by
  rcases hK.exists_open_superset_measure_lt_top μ with ⟨V, hKV, hVo, hμV⟩
  have := Fact.mk hμV
  obtain ⟨U, hKU, hUo, hμU⟩ : exists U, K subseteq U ∧ IsOpen U ∧ μ.restrict V U < r :=
exists_isOpen_lt_of_lt K r (restrict_apply_le _ _).trans_lt hr
  refine ⟨U inter V, subset_inter hKU hKV, hUo.inter hVo, ?_⟩
  rwa [restrict_apply hUo.measurableSet] at hμU

/--
lemma `_root_.IsCompact.measure_eq_iInf_isOpen` / 引理 `_root_.IsCompact.measure_eq_iInf_isOpen`

English:
lemma _root_.IsCompact.measure_eq_iInf_isOpen
  statement: [InnerRegularCompactLTTop μ]
  proof: by
  apply le_antisymm
  · simp only [le_iInf_iff]
    exact fun U KU _ => measure_mono KU
  · apply le_of_forall_gt
    simpa only [iInf_lt_iff, exists_prop, exists_and_left] using hK.exists_isOpen_lt_of_lt

中文:
引理 _root_.IsCompact.measure_eq_iInf_isOpen
  结论: [InnerRegularCompactLTTop μ]
  证明: by
  apply le_antisymm
  · simp only [le_iInf_iff]
    exact fun U KU _ => measure_mono KU
  · apply le_of_forall_gt
    simpa only [iInf_lt_iff, exists_prop, exists_and_left] using hK.exists_isOpen_lt_of_lt
-/
protected lemma _root_.IsCompact.measure_eq_iInf_isOpen [InnerRegularCompactLTTop μ]
    [IsLocallyFiniteMeasure μ] [R1Space α] [BorelSpace α] {K : Set α} (hK : IsCompact K) :
    μ K = ⨅ (U : Set α) (_ : K subseteq U) (_ : IsOpen U), μ U := by
  apply le_antisymm
  · simp only [le_iInf_iff]
    exact fun U KU _ => measure_mono KU
  · apply le_of_forall_gt
    simpa only [iInf_lt_iff, exists_prop, exists_and_left] using hK.exists_isOpen_lt_of_lt

/--
theorem `_root_.IsCompact.exists_isOpen_lt_add` / 定理 `_root_.IsCompact.exists_isOpen_lt_add`

English:
theorem _root_.IsCompact.exists_isOpen_lt_add
  statement: [InnerRegularCompactLTTop μ]
  proof: hK.exists_isOpen_lt_of_lt _ (ENNReal.lt_add_right hK.measure_lt_top.ne hε)

中文:
定理 _root_.IsCompact.exists_isOpen_lt_add
  结论: [InnerRegularCompactLTTop μ]
  证明: hK.exists_isOpen_lt_of_lt _ (ENNReal.lt_add_right hK.measure_lt_top.ne hε)
-/
protected theorem _root_.IsCompact.exists_isOpen_lt_add [InnerRegularCompactLTTop μ]
    [IsLocallyFiniteMeasure μ] [R1Space α] [BorelSpace α]
    {K : Set α} (hK : IsCompact K) {ε : Real>=0∞} (hε : ε != 0) :
    exists U, K subseteq U ∧ IsOpen U ∧ μ U < μ K + ε :=
  hK.exists_isOpen_lt_of_lt _ (ENNReal.lt_add_right hK.measure_lt_top.ne hε)

/--
theorem `_root_.MeasurableSet.exists_isOpen_symmDiff_lt` / 定理 `_root_.MeasurableSet.exists_isOpen_symmDiff_lt`

English:
theorem _root_.MeasurableSet.exists_isOpen_symmDiff_lt
  statement: [InnerRegularCompactLTTop μ]
  proof: by
  have : ε / 2 != 0 := (ENNReal.half_pos hε).ne'
  rcases hs.exists_isCompact_isClosed_sdiff_lt hμs this with ⟨K, hKs, hKco, hKcl, hμK⟩
  rcases hKco.exists_isOpen_lt_add (μ := μ) this with ⟨U, hKU, hUo, hμU⟩
  refine ⟨U, hUo, hμU.trans_le le_top, ?_⟩
  rw [← ENNReal.add_halves ε]; rw [measure_sy

中文:
定理 _root_.MeasurableSet.exists_isOpen_symmDiff_lt
  结论: [InnerRegularCompactLTTop μ]
  证明: by
  have : ε / 2 != 0 := (ENNReal.half_pos hε).ne'
  rcases hs.exists_isCompact_isClosed_sdiff_lt hμs this with ⟨K, hKs, hKco, hKcl, hμK⟩
  rcases hKco.exists_isOpen_lt_add (μ := μ) this with ⟨U, hKU, hUo, hμU⟩
  refine ⟨U, hUo, hμU.trans_le le_top, ?_⟩
  rw [← ENNReal.add_halves ε]; rw [measure_sy
-/
protected theorem _root_.MeasurableSet.exists_isOpen_symmDiff_lt [InnerRegularCompactLTTop μ]
    [IsLocallyFiniteMeasure μ] [R1Space α] [BorelSpace α]
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s != ∞) {ε : Real>=0∞} (hε : ε != 0) :
    exists U, IsOpen U ∧ μ U < ∞ ∧ μ (U ∆ s) < ε := by
  have : ε / 2 != 0 := (ENNReal.half_pos hε).ne'
  rcases hs.exists_isCompact_isClosed_sdiff_lt hμs this with ⟨K, hKs, hKco, hKcl, hμK⟩
  rcases hKco.exists_isOpen_lt_add (μ := μ) this with ⟨U, hKU, hUo, hμU⟩
  refine ⟨U, hUo, hμU.trans_le le_top, ?_⟩
  rw [← ENNReal.add_halves ε]; rw [measure_symmDiff_eq hUo.nullMeasurableSet hs.nullMeasurableSet]
  gcongr
  · calc
      μ (U \ s) <= μ (U \ K) := by gcongr
      _ < ε / 2 := by
        apply measure_sdiff_lt_of_lt_add hKcl.nullMeasurableSet hKU _ hμU
        exact ne_top_of_le_ne_top hμs (by gcongr)
  · exact lt_of_le_of_lt (by gcongr) hμK

/--
theorem `_root_.MeasureTheory.NullMeasurableSet.exists_isOpen_symmDiff_lt` / 定理 `_root_.MeasureTheory.NullMeasurableSet.exists_isOpen_symmDiff_lt`

English:
theorem _root_.MeasureTheory.NullMeasurableSet.exists_isOpen_symmDiff_lt
  proof: by
  rcases hs with ⟨t, htm, hst⟩
  rcases htm.exists_isOpen_symmDiff_lt (by rwa [← measure_congr hst]) hε with ⟨U, hUo, hμU, hUs⟩
  refine ⟨U, hUo, hμU, ?_⟩
  rwa [measure_congr <| (ae_eq_refl _).symmDiff hst]

中文:
定理 _root_.MeasureTheory.NullMeasurableSet.exists_isOpen_symmDiff_lt
  证明: by
  rcases hs with ⟨t, htm, hst⟩
  rcases htm.exists_isOpen_symmDiff_lt (by rwa [← measure_congr hst]) hε with ⟨U, hUo, hμU, hUs⟩
  refine ⟨U, hUo, hμU, ?_⟩
  rwa [measure_congr <| (ae_eq_refl _).symmDiff hst]
-/
protected theorem _root_.MeasureTheory.NullMeasurableSet.exists_isOpen_symmDiff_lt
    [InnerRegularCompactLTTop μ] [IsLocallyFiniteMeasure μ] [R1Space α] [BorelSpace α]
    {s : Set α} (hs : NullMeasurableSet s μ) (hμs : μ s != ∞) {ε : Real>=0∞} (hε : ε != 0) :
    exists U, IsOpen U ∧ μ U < ∞ ∧ μ (U ∆ s) < ε := by
  rcases hs with ⟨t, htm, hst⟩
  rcases htm.exists_isOpen_symmDiff_lt (by rwa [← measure_congr hst]) hε with ⟨U, hUo, hμU, hUs⟩
  refine ⟨U, hUo, hμU, ?_⟩
  rwa [measure_congr <| (ae_eq_refl _).symmDiff hst]

/--
Instance `smul` / 实例 `smul`

English:
instance smul
  signature: [h : InnerRegularCompactLTTop μ] (c : Real>=0∞)
  body: by
  by_cases hc : c = 0
  · simp only [hc, zero_smul]
    infer_instance
  by_cases h'c : c = ∞
  · constructor
    intro s hs r hr
    by_cases h's : μ s = 0
    · simp [h's] at hr
    · simp [h'c, h's] at hs
  · constructor
    convert! InnerRegularWRT.smul h.innerRegular c using 2 with s
    hav

中文:
实例 smul
  签名: [h : InnerRegularCompactLTTop μ] (c : 实数>=0∞)
  定义体: by
  by_cases hc : c = 0
  · simp only [hc, zero_smul]
    infer_instance
  by_cases h'c : c = ∞
  · constructor
    intro s hs r hr
    by_cases h's : μ s = 0
    · simp [h's] at hr
    · simp [h'c, h's] at hs
  · constructor
    convert! InnerRegularWRT.smul h.innerRegular c using 2 with s
    hav

Depends on / 依赖: ENNReal, ENNReal.mul_eq_top, InnerRegularWRT, InnerRegularWRT.smul, convert, h.innerRegular, infer_instance, innerRegular, mul_eq_top, zero_smul
-/
instance smul [h : InnerRegularCompactLTTop μ] (c : Real>=0∞) : InnerRegularCompactLTTop (c • μ) := by
  by_cases hc : c = 0
  · simp only [hc, zero_smul]
    infer_instance
  by_cases h'c : c = ∞
  · constructor
    intro s hs r hr
    by_cases h's : μ s = 0
    · simp [h's] at hr
    · simp [h'c, h's] at hs
  · constructor
    convert! InnerRegularWRT.smul h.innerRegular c using 2 with s
    have : (c • μ) s != ∞ ↔ μ s != ∞ := by simp [ENNReal.mul_eq_top, hc, h'c]
    simp only [this]

/--
Instance `smul_nnreal` / 实例 `smul_nnreal`

English:
instance smul_nnreal
  signature: [InnerRegularCompactLTTop μ] (c : Real>=0)
  body: inferInstanceAs (InnerRegularCompactLTTop ((c : Real>=0∞) • μ))

中文:
实例 smul_nnreal
  签名: [InnerRegularCompactLTTop μ] (c : 实数>=0)
  定义体: inferInstanceAs (InnerRegularCompactLTTop ((c : Real>=0∞) • μ))

Depends on / 依赖: InnerRegularCompactLTTop
-/
instance smul_nnreal [InnerRegularCompactLTTop μ] (c : Real>=0) :
    InnerRegularCompactLTTop (c • μ) :=
  inferInstanceAs (InnerRegularCompactLTTop ((c : Real>=0∞) • μ))

instance (priority := 80) [InnerRegularCompactLTTop μ] [SigmaFinite μ] : InnerRegular μ :=
  ⟨InnerRegularCompactLTTop.innerRegular.trans InnerRegularWRT.of_sigmaFinite⟩

/--
theorem `map_of_continuous` / 定理 `map_of_continuous`

English:
theorem map_of_continuous
  statement: [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
  proof: by
  constructor
  refine InnerRegularWRT.map h.innerRegular hf.aemeasurable ?_ (fun K hK => hK.image hf) ?_
  · rintro s ⟨hs, h's⟩
    exact ⟨hf.measurable hs, by rwa [map_apply hf.measurable hs] at h's⟩
  · rintro s ⟨hs, -⟩
    exact hs

中文:
定理 map_of_continuous
  结论: [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
  证明: by
  constructor
  refine InnerRegularWRT.map h.innerRegular hf.aemeasurable ?_ (fun K hK => hK.image hf) ?_
  · rintro s ⟨hs, h's⟩
    exact ⟨hf.measurable hs, by rwa [map_apply hf.measurable hs] at h's⟩
  · rintro s ⟨hs, -⟩
    exact hs
-/
protected theorem map_of_continuous [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] [h : InnerRegularCompactLTTop μ] {f : α -> β} (hf : Continuous f) :
    InnerRegularCompactLTTop (Measure.map f μ) := by
  constructor
  refine InnerRegularWRT.map h.innerRegular hf.aemeasurable ?_ (fun K hK => hK.image hf) ?_
  · rintro s ⟨hs, h's⟩
    exact ⟨hf.measurable hs, by rwa [map_apply hf.measurable hs] at h's⟩
  · rintro s ⟨hs, -⟩
    exact hs

end InnerRegularCompactLTTop

-- Generalized and moved to another file

namespace WeaklyRegular

variable [TopologicalSpace α]

/--
Instance `zero` / 实例 `zero`

English:
instance zero
  signature: : WeaklyRegular (0 : Measure α)
  body: ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isClosed_empty, hr⟩⟩

中文:
实例 zero
  签名: : WeaklyRegular (0 : Measure α)
  定义体: ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isClosed_empty, hr⟩⟩

Depends on / 依赖: empty_subset, isClosed_empty
-/
instance zero : WeaklyRegular (0 : Measure α) :=
  ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isClosed_empty, hr⟩⟩

/--
theorem `_root_.IsOpen.exists_lt_isClosed` / 定理 `_root_.IsOpen.exists_lt_isClosed`

English:
theorem _root_.IsOpen.exists_lt_isClosed
  given: [WeaklyRegular μ] ⦃U
  statement: Set α⦄ (hU : IsOpen U) {r : Real>=0∞}
  proof: WeaklyRegular.innerRegular hU r hr

中文:
定理 _root_.IsOpen.exists_lt_isClosed
  条件: [WeaklyRegular μ] ⦃U
  结论: Set α⦄ (hU : IsOpen U) {r : 实数>=0∞}
  证明: WeaklyRegular.innerRegular hU r hr

Depends on / 依赖: WeaklyRegular, WeaklyRegular.innerRegular, innerRegular
-/
theorem _root_.IsOpen.exists_lt_isClosed [WeaklyRegular μ] ⦃U : Set α⦄ (hU : IsOpen U) {r : Real>=0∞}
    (hr : r < μ U) : exists F, F subseteq U ∧ IsClosed F ∧ r < μ F :=
  WeaklyRegular.innerRegular hU r hr

/--
theorem `_root_.IsOpen.measure_eq_iSup_isClosed` / 定理 `_root_.IsOpen.measure_eq_iSup_isClosed`

English:
theorem _root_.IsOpen.measure_eq_iSup_isClosed
  given: ⦃U
  statement: Set α⦄ (hU : IsOpen U) (μ : Measure α)
  proof: WeaklyRegular.innerRegular.measure_eq_iSup hU

中文:
定理 _root_.IsOpen.measure_eq_iSup_isClosed
  条件: ⦃U
  结论: Set α⦄ (hU : IsOpen U) (μ : Measure α)
  证明: WeaklyRegular.innerRegular.measure_eq_iSup hU

Depends on / 依赖: WeaklyRegular, WeaklyRegular.innerRegular.measure_eq_iSup, innerRegular, measure_eq_iSup
-/
theorem _root_.IsOpen.measure_eq_iSup_isClosed ⦃U : Set α⦄ (hU : IsOpen U) (μ : Measure α)
    [WeaklyRegular μ] : μ U = ⨆ (F) (_ : F subseteq U) (_ : IsClosed F), μ F :=
  WeaklyRegular.innerRegular.measure_eq_iSup hU

/--
theorem `innerRegular_measurable` / 定理 `innerRegular_measurable`

English:
theorem innerRegular_measurable
  given: [WeaklyRegular μ]
  proof: WeaklyRegular.innerRegular.measurableSet_of_isOpen (fun _ _ h₁ h₂ => h₁.inter h₂.isClosed_compl)

中文:
定理 innerRegular_measurable
  条件: [WeaklyRegular μ]
  证明: WeaklyRegular.innerRegular.measurableSet_of_isOpen (fun _ _ h₁ h₂ => h₁.inter h₂.isClosed_compl)

Depends on / 依赖: WeaklyRegular, WeaklyRegular.innerRegular.measurableSet_of_isOpen, innerRegular, isClosed_compl, measurableSet_of_isOpen
-/
theorem innerRegular_measurable [WeaklyRegular μ] :
    InnerRegularWRT μ IsClosed fun s => MeasurableSet s ∧ μ s != ∞ :=
  WeaklyRegular.innerRegular.measurableSet_of_isOpen (fun _ _ h₁ h₂ => h₁.inter h₂.isClosed_compl)

/--
theorem `_root_.MeasurableSet.exists_isClosed_lt_add` / 定理 `_root_.MeasurableSet.exists_isClosed_lt_add`

English:
theorem _root_.MeasurableSet.exists_isClosed_lt_add
  statement: [WeaklyRegular μ] {s : Set α}
  proof: innerRegular_measurable.exists_subset_lt_add isClosed_empty ⟨hs, hμs⟩ hμs hε

中文:
定理 _root_.MeasurableSet.exists_isClosed_lt_add
  结论: [WeaklyRegular μ] {s : Set α}
  证明: innerRegular_measurable.exists_subset_lt_add isClosed_empty ⟨hs, hμs⟩ hμs hε

Depends on / 依赖: exists_subset_lt_add, innerRegular_measurable, innerRegular_measurable.exists_subset_lt_add, isClosed_empty
-/
theorem _root_.MeasurableSet.exists_isClosed_lt_add [WeaklyRegular μ] {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s != ∞) {ε : Real>=0∞} (hε : ε != 0) :
    exists K, K subseteq s ∧ IsClosed K ∧ μ s < μ K + ε :=
  innerRegular_measurable.exists_subset_lt_add isClosed_empty ⟨hs, hμs⟩ hμs hε

/--
theorem `_root_.MeasurableSet.exists_isClosed_sdiff_lt` / 定理 `_root_.MeasurableSet.exists_isClosed_sdiff_lt`

English:
theorem _root_.MeasurableSet.exists_isClosed_sdiff_lt
  statement: [OpensMeasurableSpace α] [WeaklyRegular μ]
  proof: by
  rcases hA.exists_isClosed_lt_add h'A hε with ⟨F, hFA, hFc, hF⟩
  exact ⟨F, hFA, hFc, measure_sdiff_lt_of_lt_add hFc.nullMeasurableSet hFA
    (ne_top_of_le_ne_top h'A <| measure_mono hFA) hF⟩

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isClosed_diff_lt := _root_.Mea

中文:
定理 _root_.MeasurableSet.exists_isClosed_sdiff_lt
  结论: [OpensMeasurableSpace α] [WeaklyRegular μ]
  证明: by
  rcases hA.exists_isClosed_lt_add h'A hε with ⟨F, hFA, hFc, hF⟩
  exact ⟨F, hFA, hFc, measure_sdiff_lt_of_lt_add hFc.nullMeasurableSet hFA
    (ne_top_of_le_ne_top h'A <| measure_mono hFA) hF⟩

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isClosed_diff_lt := _root_.Mea

Depends on / 依赖: exists_isClosed_lt_add, hA.exists_isClosed_lt_add, hFc.nullMeasurableSet, measure_mono, measure_sdiff_lt_of_lt_add, ne_top_of_le_ne_top, nullMeasurableSet
-/
theorem _root_.MeasurableSet.exists_isClosed_sdiff_lt [OpensMeasurableSpace α] [WeaklyRegular μ]
    ⦃A : Set α⦄ (hA : MeasurableSet A) (h'A : μ A != ∞) {ε : Real>=0∞} (hε : ε != 0) :
    exists F, F subseteq A ∧ IsClosed F ∧ μ (A \ F) < ε := by
  rcases hA.exists_isClosed_lt_add h'A hε with ⟨F, hFA, hFc, hF⟩
  exact ⟨F, hFA, hFc, measure_sdiff_lt_of_lt_add hFc.nullMeasurableSet hFA
    (ne_top_of_le_ne_top h'A <| measure_mono hFA) hF⟩

@[deprecated (since := "2026-06-03")]
alias _root_.MeasurableSet.exists_isClosed_diff_lt := _root_.MeasurableSet.exists_isClosed_sdiff_lt

/--
theorem `_root_.MeasurableSet.exists_lt_isClosed_of_ne_top` / 定理 `_root_.MeasurableSet.exists_lt_isClosed_of_ne_top`

English:
theorem _root_.MeasurableSet.exists_lt_isClosed_of_ne_top
  given: [WeaklyRegular μ] ⦃A
  statement: Set α⦄
  proof: innerRegular_measurable ⟨hA, h'A⟩ _ hr

中文:
定理 _root_.MeasurableSet.exists_lt_isClosed_of_ne_top
  条件: [WeaklyRegular μ] ⦃A
  结论: Set α⦄
  证明: innerRegular_measurable ⟨hA, h'A⟩ _ hr

Depends on / 依赖: innerRegular_measurable
-/
theorem _root_.MeasurableSet.exists_lt_isClosed_of_ne_top [WeaklyRegular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A != ∞) {r : Real>=0∞} (hr : r < μ A) :
    exists K, K subseteq A ∧ IsClosed K ∧ r < μ K :=
  innerRegular_measurable ⟨hA, h'A⟩ _ hr

/--
theorem `_root_.MeasurableSet.measure_eq_iSup_isClosed_of_ne_top` / 定理 `_root_.MeasurableSet.measure_eq_iSup_isClosed_of_ne_top`

English:
theorem _root_.MeasurableSet.measure_eq_iSup_isClosed_of_ne_top
  given: [WeaklyRegular μ] ⦃A
  statement: Set α⦄
  proof: innerRegular_measurable.measure_eq_iSup ⟨hA, h'A⟩

中文:
定理 _root_.MeasurableSet.measure_eq_iSup_isClosed_of_ne_top
  条件: [WeaklyRegular μ] ⦃A
  结论: Set α⦄
  证明: innerRegular_measurable.measure_eq_iSup ⟨hA, h'A⟩

Depends on / 依赖: innerRegular_measurable, innerRegular_measurable.measure_eq_iSup, measure_eq_iSup
-/
theorem _root_.MeasurableSet.measure_eq_iSup_isClosed_of_ne_top [WeaklyRegular μ] ⦃A : Set α⦄
    (hA : MeasurableSet A) (h'A : μ A != ∞) : μ A = ⨆ (K) (_ : K subseteq A) (_ : IsClosed K), μ K :=
  innerRegular_measurable.measure_eq_iSup ⟨hA, h'A⟩

/--
theorem `restrict_of_measure_ne_top` / 定理 `restrict_of_measure_ne_top`

English:
theorem restrict_of_measure_ne_top
  statement: [BorelSpace α] [WeaklyRegular μ] {A : Set α}
  proof: by
  have : Fact (μ A < ∞) := ⟨h'A.lt_top⟩
  refine InnerRegularWRT.weaklyRegular_of_finite (μ.restrict A) (fun V V_open r hr => ?_)
  have : InnerRegularWRT (μ.restrict A) IsClosed (fun s => MeasurableSet s) :=
    InnerRegularWRT.restrict_of_measure_ne_top innerRegular_measurable h'A
  exact this 

中文:
定理 restrict_of_measure_ne_top
  结论: [BorelSpace α] [WeaklyRegular μ] {A : Set α}
  证明: by
  have : Fact (μ A < ∞) := ⟨h'A.lt_top⟩
  refine InnerRegularWRT.weaklyRegular_of_finite (μ.restrict A) (fun V V_open r hr => ?_)
  have : InnerRegularWRT (μ.restrict A) IsClosed (fun s => MeasurableSet s) :=
    InnerRegularWRT.restrict_of_measure_ne_top innerRegular_measurable h'A
  exact this 

Depends on / 依赖: A.lt_top, InnerRegularWRT, InnerRegularWRT.restrict_of_measure_ne_top, InnerRegularWRT.weaklyRegular_of_finite, IsClosed, MeasurableSet, V_open, V_open.measurableSet, innerRegular_measurable, lt_top, measurableSet, restrict, restrict_of_measure_ne_top, weaklyRegular_of_finite
-/
theorem restrict_of_measure_ne_top [BorelSpace α] [WeaklyRegular μ] {A : Set α}
    (h'A : μ A != ∞) : WeaklyRegular (μ.restrict A) := by
  have : Fact (μ A < ∞) := ⟨h'A.lt_top⟩
  refine InnerRegularWRT.weaklyRegular_of_finite (μ.restrict A) (fun V V_open r hr => ?_)
  have : InnerRegularWRT (μ.restrict A) IsClosed (fun s => MeasurableSet s) :=
    InnerRegularWRT.restrict_of_measure_ne_top innerRegular_measurable h'A
  exact this V_open.measurableSet r hr

-- see Note [lower instance priority]
/-- Any finite measure on a metrizable space (or even a pseudometrizable space)
is weakly regular. -/
instance (priority := 100) of_pseudoMetrizableSpace_of_isFiniteMeasure {X : Type*}
    [TopologicalSpace X] [PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] :
    WeaklyRegular μ :=
  (InnerRegularWRT.of_pseudoMetrizableSpace μ).weaklyRegular_of_finite μ

-- see Note [lower instance priority]
/-- Any locally finite measure on a second countable metrizable space
(or even a pseudometrizable space) is weakly regular. -/
instance (priority := 100) of_pseudoMetrizableSpace_secondCountable_of_locallyFinite {X : Type*}
    [TopologicalSpace X] [PseudoMetrizableSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ] : WeaklyRegular μ :=
  have : OuterRegular μ := by
    refine (μ.finiteSpanningSetsInOpen'.mono' fun U hU => ?_).outerRegular
    have : Fact (μ U < ∞) := ⟨hU.2⟩
    exact ⟨hU.1, inferInstance⟩
  ⟨InnerRegularWRT.of_pseudoMetrizableSpace μ⟩

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: [WeaklyRegular μ] {x : Real>=0∞} (hx : x != ∞)
  statement: (x • μ).WeaklyRegular
  proof: by
  have := OuterRegular.smul μ hx
  exact ⟨WeaklyRegular.innerRegular.smul x⟩

中文:
定理 smul
  条件: [WeaklyRegular μ] {x : 实数>=0∞} (hx : x != ∞)
  结论: (x • μ).WeaklyRegular
  证明: by
  have := OuterRegular.smul μ hx
  exact ⟨WeaklyRegular.innerRegular.smul x⟩
-/
protected theorem smul [WeaklyRegular μ] {x : Real>=0∞} (hx : x != ∞) : (x • μ).WeaklyRegular := by
  have := OuterRegular.smul μ hx
  exact ⟨WeaklyRegular.innerRegular.smul x⟩

/--
Instance `smul_nnreal` / 实例 `smul_nnreal`

English:
instance smul_nnreal
  signature: [WeaklyRegular μ] (c : Real>=0)
  body: WeaklyRegular.smul coe_ne_top

中文:
实例 smul_nnreal
  签名: [WeaklyRegular μ] (c : 实数>=0)
  定义体: WeaklyRegular.smul coe_ne_top

Depends on / 依赖: WeaklyRegular, WeaklyRegular.smul, coe_ne_top
-/
instance smul_nnreal [WeaklyRegular μ] (c : Real>=0) : WeaklyRegular (c • μ) :=
  WeaklyRegular.smul coe_ne_top

end WeaklyRegular

namespace Regular

variable [TopologicalSpace α]

/--
Instance `zero` / 实例 `zero`

English:
instance zero
  signature: : Regular (0 : Measure α)
  body: ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isCompact_empty, hr⟩⟩

中文:
实例 zero
  签名: : Regular (0 : Measure α)
  定义体: ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isCompact_empty, hr⟩⟩

Depends on / 依赖: empty_subset, isCompact_empty
-/
instance zero : Regular (0 : Measure α) :=
  ⟨fun _ _ _r hr => ⟨∅, empty_subset _, isCompact_empty, hr⟩⟩

/--
theorem `_root_.IsOpen.exists_lt_isCompact` / 定理 `_root_.IsOpen.exists_lt_isCompact`

English:
theorem _root_.IsOpen.exists_lt_isCompact
  given: [Regular μ] ⦃U
  statement: Set α⦄ (hU : IsOpen U) {r : Real>=0∞}
  proof: Regular.innerRegular hU r hr

中文:
定理 _root_.IsOpen.exists_lt_isCompact
  条件: [Regular μ] ⦃U
  结论: Set α⦄ (hU : IsOpen U) {r : 实数>=0∞}
  证明: Regular.innerRegular hU r hr

Depends on / 依赖: Regular, Regular.innerRegular, innerRegular
-/
theorem _root_.IsOpen.exists_lt_isCompact [Regular μ] ⦃U : Set α⦄ (hU : IsOpen U) {r : Real>=0∞}
    (hr : r < μ U) : exists K, K subseteq U ∧ IsCompact K ∧ r < μ K :=
  Regular.innerRegular hU r hr

/--
theorem `_root_.IsOpen.measure_eq_iSup_isCompact` / 定理 `_root_.IsOpen.measure_eq_iSup_isCompact`

English:
theorem _root_.IsOpen.measure_eq_iSup_isCompact
  given: ⦃U
  statement: Set α⦄ (hU : IsOpen U) (μ : Measure α)
  proof: Regular.innerRegular.measure_eq_iSup hU

中文:
定理 _root_.IsOpen.measure_eq_iSup_isCompact
  条件: ⦃U
  结论: Set α⦄ (hU : IsOpen U) (μ : Measure α)
  证明: Regular.innerRegular.measure_eq_iSup hU

Depends on / 依赖: Regular, Regular.innerRegular.measure_eq_iSup, innerRegular, measure_eq_iSup
-/
theorem _root_.IsOpen.measure_eq_iSup_isCompact ⦃U : Set α⦄ (hU : IsOpen U) (μ : Measure α)
    [Regular μ] : μ U = ⨆ (K : Set α) (_ : K subseteq U) (_ : IsCompact K), μ K :=
  Regular.innerRegular.measure_eq_iSup hU

/--
theorem `exists_isCompact_not_null` / 定理 `exists_isCompact_not_null`

English:
theorem exists_isCompact_not_null
  given: [Regular μ]
  statement: (exists K, IsCompact K ∧ μ K != 0) ↔ μ != 0
  proof: by
  simp_rw [Ne, ← measure_univ_eq_zero, isOpen_univ.measure_eq_iSup_isCompact,
    ENNReal.iSup_eq_zero, not_forall, exists_prop, subset_univ, true_and]

中文:
定理 exists_isCompact_not_null
  条件: [Regular μ]
  结论: (存在 K, IsCompact K ∧ μ K != 0) ↔ μ != 0
  证明: by
  simp_rw [Ne, ← measure_univ_eq_zero, isOpen_univ.measure_eq_iSup_isCompact,
    ENNReal.iSup_eq_zero, not_forall, exists_prop, subset_univ, true_and]

Depends on / 依赖: BddDistLat, BddDistLat.ofHom, ENNReal, ENNReal.iSup_eq_zero, exists_prop, iSup_eq_zero, isOpen_univ, isOpen_univ.measure_eq_iSup_isCompact, measure_eq_iSup_isCompact, measure_univ_eq_zero, not_forall, simp_rw, subset_univ, true_and
-/
theorem exists_isCompact_not_null [Regular μ] : (exists K, IsCompact K ∧ μ K != 0) ↔ μ != 0 := by
  simp_rw [Ne, ← measure_univ_eq_zero, isOpen_univ.measure_eq_iSup_isCompact,
    ENNReal.iSup_eq_zero, not_forall, exists_prop, subset_univ, true_and]
/-- If `μ` is a regular measure, then any measurable set of finite measure can be approximated by a
compact subset. See also `MeasurableSet.exists_isCompact_lt_add` and
`MeasurableSet.exists_lt_isCompact_of_ne_top`. -/
instance (priority := 100) [Regular μ] : InnerRegularCompactLTTop μ :=
  ⟨Regular.innerRegular.measurableSet_of_isOpen (fun _ _ hs hU => hs.diff hU)⟩

/--
theorem `map` / 定理 `map`

English:
theorem map
  statement: [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
  proof: by
  have := OuterRegular.map f μ
  have := IsFiniteMeasureOnCompacts.map μ f
  exact
    ⟨Regular.innerRegular.map' f.toMeasurableEquiv
        (fun U hU => hU.preimage f.continuous)
        (fun K hK => hK.image f.continuous)⟩

中文:
定理 map
  结论: [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
  证明: by
  have := OuterRegular.map f μ
  have := IsFiniteMeasureOnCompacts.map μ f
  exact
    ⟨Regular.innerRegular.map' f.toMeasurableEquiv
        (fun U hU => hU.preimage f.continuous)
        (fun K hK => hK.image f.continuous)⟩
-/
protected theorem map [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] [Regular μ] (f : α ≃ₜ β) : (Measure.map f μ).Regular := by
  have := OuterRegular.map f μ
  have := IsFiniteMeasureOnCompacts.map μ f
  exact
    ⟨Regular.innerRegular.map' f.toMeasurableEquiv
        (fun U hU => hU.preimage f.continuous)
        (fun K hK => hK.image f.continuous)⟩

/--
theorem `map_iff` / 定理 `map_iff`

English:
theorem map_iff
  statement: [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
  proof: by
  refine ⟨fun h => ?_, fun h => h.map f⟩
  convert! h.map f.symm
  rw [map_map f.symm.continuous.measurable f.continuous.measurable]
  simp

中文:
定理 map_iff
  结论: [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
  证明: by
  refine ⟨fun h => ?_, fun h => h.map f⟩
  convert! h.map f.symm
  rw [map_map f.symm.continuous.measurable f.continuous.measurable]
  simp
-/
protected theorem map_iff [BorelSpace α] [MeasurableSpace β] [TopologicalSpace β]
    [BorelSpace β] (f : α ≃ₜ β) :
    Regular (Measure.map f μ) ↔ Regular μ := by
  refine ⟨fun h => ?_, fun h => h.map f⟩
  convert! h.map f.symm
  rw [map_map f.symm.continuous.measurable f.continuous.measurable]
  simp

open Topology in
/--
theorem `comap'` / 定理 `comap'`

English:
theorem comap'
  statement: [BorelSpace α]
  proof: by
  have := OuterRegular.comap' μ hf.continuous hf.measurableEmbedding
  have := IsFiniteMeasureOnCompacts.comap' μ hf.continuous hf.measurableEmbedding
  exact ⟨InnerRegularWRT.comap Regular.innerRegular hf.measurableEmbedding
    (fun _ hU => hf.isOpen_iff_image_isOpen.mp hU)
    (fun _ hKrange h

中文:
定理 comap'
  结论: [BorelSpace α]
  证明: by
  have := OuterRegular.comap' μ hf.continuous hf.measurableEmbedding
  have := IsFiniteMeasureOnCompacts.comap' μ hf.continuous hf.measurableEmbedding
  exact ⟨InnerRegularWRT.comap Regular.innerRegular hf.measurableEmbedding
    (fun _ hU => hf.isOpen_iff_image_isOpen.mp hU)
    (fun _ hKrange h
-/
protected theorem comap' [BorelSpace α]
    {mβ : MeasurableSpace β} [TopologicalSpace β] [BorelSpace β] (μ : Measure β) [Regular μ]
    {f : α -> β} (hf : IsOpenEmbedding f) : (μ.comap f).Regular := by
  have := OuterRegular.comap' μ hf.continuous hf.measurableEmbedding
  have := IsFiniteMeasureOnCompacts.comap' μ hf.continuous hf.measurableEmbedding
  exact ⟨InnerRegularWRT.comap Regular.innerRegular hf.measurableEmbedding
    (fun _ hU => hf.isOpen_iff_image_isOpen.mp hU)
    (fun _ hKrange hK => hf.isInducing.isCompact_preimage' hK hKrange)⟩

/--
theorem `comap` / 定理 `comap`

English:
theorem comap
  statement: [BorelSpace α] {mβ : MeasurableSpace β} [TopologicalSpace β]
  proof: Regular.comap' μ f.isOpenEmbedding

中文:
定理 comap
  结论: [BorelSpace α] {mβ : MeasurableSpace β} [TopologicalSpace β]
  证明: Regular.comap' μ f.isOpenEmbedding
-/
protected theorem comap [BorelSpace α] {mβ : MeasurableSpace β} [TopologicalSpace β]
    [BorelSpace β] (μ : Measure β) [Regular μ] (f : α ≃ₜ β) : (μ.comap f).Regular :=
  Regular.comap' μ f.isOpenEmbedding

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: [Regular μ] {x : Real>=0∞} (hx : x != ∞)
  statement: (x • μ).Regular
  proof: by
  have := OuterRegular.smul μ hx
  have := IsFiniteMeasureOnCompacts.smul μ hx
  exact ⟨Regular.innerRegular.smul x⟩

中文:
定理 smul
  条件: [Regular μ] {x : 实数>=0∞} (hx : x != ∞)
  结论: (x • μ).Regular
  证明: by
  have := OuterRegular.smul μ hx
  have := IsFiniteMeasureOnCompacts.smul μ hx
  exact ⟨Regular.innerRegular.smul x⟩
-/
protected theorem smul [Regular μ] {x : Real>=0∞} (hx : x != ∞) : (x • μ).Regular := by
  have := OuterRegular.smul μ hx
  have := IsFiniteMeasureOnCompacts.smul μ hx
  exact ⟨Regular.innerRegular.smul x⟩

/--
Instance `smul_nnreal` / 实例 `smul_nnreal`

English:
instance smul_nnreal
  signature: [Regular μ] (c : Real>=0)
  body: Regular.smul coe_ne_top

中文:
实例 smul_nnreal
  签名: [Regular μ] (c : 实数>=0)
  定义体: Regular.smul coe_ne_top

Depends on / 依赖: Regular, Regular.smul, coe_ne_top
-/
instance smul_nnreal [Regular μ] (c : Real>=0) : Regular (c • μ) := Regular.smul coe_ne_top

/--
theorem `restrict_of_measure_ne_top` / 定理 `restrict_of_measure_ne_top`

English:
theorem restrict_of_measure_ne_top
  statement: [R1Space α] [BorelSpace α] [Regular μ]
  proof: by
  have : WeaklyRegular (μ.restrict A) := WeaklyRegular.restrict_of_measure_ne_top h'A
  constructor
  intro V hV r hr
  have R : restrict μ A V != ∞ := by
    rw [restrict_apply hV.measurableSet]
    exact ((measure_mono inter_subset_right).trans_lt h'A.lt_top).ne
  exact MeasurableSet.exists_lt_

中文:
定理 restrict_of_measure_ne_top
  结论: [R1Space α] [BorelSpace α] [Regular μ]
  证明: by
  have : WeaklyRegular (μ.restrict A) := WeaklyRegular.restrict_of_measure_ne_top h'A
  constructor
  intro V hV r hr
  have R : restrict μ A V != ∞ := by
    rw [restrict_apply hV.measurableSet]
    exact ((measure_mono inter_subset_right).trans_lt h'A.lt_top).ne
  exact MeasurableSet.exists_lt_

Depends on / 依赖: A.lt_top, MeasurableSet, MeasurableSet.exists_lt_isCompact_of_ne_top, WeaklyRegular, WeaklyRegular.restrict_of_measure_ne_top, exists_lt_isCompact_of_ne_top, hV.measurableSet, inter_subset_right, lt_top, measurableSet, measure_mono, restrict, restrict_apply, restrict_of_measure_ne_top, trans_lt
-/
theorem restrict_of_measure_ne_top [R1Space α] [BorelSpace α] [Regular μ]
    {A : Set α} (h'A : μ A != ∞) : Regular (μ.restrict A) := by
  have : WeaklyRegular (μ.restrict A) := WeaklyRegular.restrict_of_measure_ne_top h'A
  constructor
  intro V hV r hr
  have R : restrict μ A V != ∞ := by
    rw [restrict_apply hV.measurableSet]
    exact ((measure_mono inter_subset_right).trans_lt h'A.lt_top).ne
  exact MeasurableSet.exists_lt_isCompact_of_ne_top hV.measurableSet R hr

end Regular

/--
Instance `Regular.domSMul` / 实例 `Regular.domSMul`

English:
instance Regular.domSMul
  signature: {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
  body: .map .smul ((DomMulAct.mk.symm g : G)⁻¹)

中文:
实例 Regular.domSMul
  签名: {G A : 类型} [Group G] [AddCommGroup A] [DistribMulAction G A]
  定义体: .map .smul ((DomMulAct.mk.symm g : G)⁻¹)

Depends on / 依赖: DomMulAct, DomMulAct.mk.symm
-/
instance Regular.domSMul {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
    [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A] [ContinuousConstSMul G A]
    {μ : Measure A} (g : Gᵈᵐᵃ) [Regular μ] : Regular (g • μ) :=
.map .smul ((DomMulAct.mk.symm g : G)⁻¹)

-- see Note [lower instance priority]
/-- Any locally finite measure on a `σ`-compact pseudometrizable space is regular. -/
instance (priority := 100) Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure {X : Type*}
    [TopologicalSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ] : Regular μ := by
  let A : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  exact ⟨(InnerRegularWRT.isCompact_isClosed μ).trans (InnerRegularWRT.of_pseudoMetrizableSpace μ)⟩

/-- Any sigma finite measure on a `σ`-compact pseudometrizable space is inner regular. -/
instance (priority := 100) {X : Type*}
    [TopologicalSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [SigmaFinite μ] : InnerRegular μ := by
  refine ⟨(InnerRegularWRT.isCompact_isClosed μ).trans ?_⟩
  refine InnerRegularWRT.of_restrict (fun n => ?_) (iUnion_spanningSets μ).superset
    (monotone_spanningSets μ)
  have : Fact (μ (spanningSets μ n) < ∞) := ⟨measure_spanningSets_lt_top μ n⟩
  exact WeaklyRegular.innerRegular_measurable.trans InnerRegularWRT.of_sigmaFinite

end Measure

end MeasureTheory
