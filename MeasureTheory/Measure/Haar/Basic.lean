/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Measure.Content
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.Topology.Algebra.Group.Compact

/-!
# Haar measure

In this file we prove the existence of Haar measure for a locally compact Hausdorff topological
group.

We follow the write-up by Jonathan Gleason, *Existence and Uniqueness of Haar Measure*.
This is essentially the same argument as in
https://en.wikipedia.org/wiki/Haar_measure#A_construction_using_compact_subsets.

We construct the Haar measure first on compact sets. For this we define `(K : U)` as the (smallest)
number of left-translates of `U` that are needed to cover `K` (`index` in the formalization).
Then we define a function `h` on compact sets as `lim_U (K : U) / (K₀ : U)`,
where `U` becomes a smaller and smaller open neighborhood of `1`, and `K₀` is a fixed compact set
with nonempty interior. This function is `chaar` in the formalization, and we define the limit
formally using Tychonoff's theorem.

This function `h` forms a content, which we can extend to an outer measure and then a measure
(`haarMeasure`).
We normalize the Haar measure so that the measure of `K₀` is `1`.

Note that `μ` need not coincide with `h` on compact sets, according to
[halmos1950measure, ch. X, §53 p.233]. However, we know that `h(K)` lies between `μ(Kᵒ)` and `μ(K)`,
where `ᵒ` denotes the interior.

We also give a form of uniqueness of Haar measure, for σ-finite measures on second-countable
locally compact groups. For more involved statements not assuming second-countability, see
the file `Mathlib/MeasureTheory/Measure/Haar/Unique.lean`.

## Main Declarations

* `haarMeasure`: the Haar measure on a locally compact Hausdorff group. This is a left invariant
  regular measure. It takes as argument a compact set of the group (with non-empty interior),
  and is normalized so that the measure of the given set is 1.
* `haarMeasure_self`: the Haar measure is normalized.
* `isMulLeftInvariant_haarMeasure`: the Haar measure is left invariant.
* `regular_haarMeasure`: the Haar measure is a regular measure.
* `isHaarMeasure_haarMeasure`: the Haar measure satisfies the `IsHaarMeasure` typeclass, i.e.,
  it is invariant and gives finite mass to compact sets and positive mass to nonempty open sets.
* `haar` : some choice of a Haar measure, on a locally compact Hausdorff group, constructed as
  `haarMeasure K` where `K` is some arbitrary choice of a compact set with nonempty interior.
* `haarMeasure_unique`: Every σ-finite left invariant measure on a second-countable locally compact
  Hausdorff group is a scalar multiple of the Haar measure.

## References
* Paul Halmos (1950), Measure Theory, §53
* Jonathan Gleason, Existence and Uniqueness of Haar Measure
  - Note: step 9, page 8 contains a mistake: the last defined `μ` does not extend the `μ` on compact
    sets, see Halmos (1950) p. 233, bottom of the page. This makes some other steps (like step 11)
    invalid.
* https://en.wikipedia.org/wiki/Haar_measure
-/

@[expose] public section


noncomputable section

open Set Inv Function TopologicalSpace MeasurableSpace

open scoped NNReal ENNReal Pointwise Topology

namespace MeasureTheory

namespace Measure

section Group

variable {G : Type*} [Group G]

/-! We put the internal functions in the construction of the Haar measure in a namespace,
  so that the chosen names don't clash with other declarations.
  We first define a couple of the functions before proving the properties (that require that `G`
  is a topological group). -/


namespace haar

/-- The index or Haar covering number or ratio of `K` w.r.t. `V`, denoted `(K : V)`:
  it is the smallest number of (left) translates of `V` that is necessary to cover `K`.
  It is defined to be 0 if no finite number of translates cover `K`. -/
@[to_additive addIndex /-- additive version of `MeasureTheory.Measure.haar.index` -/]
/--
Definition of `index` / `index` 的定义

English:
definition index
  signature: (K V : Set G)
  body: sInf Finset.card '' { t : Finset G | K subseteq ⋃ g in t, (fun h => g * h) ⁻¹' V }

@[to_additive addIndex_empty]

中文:
定义 index
  签名: (K V : Set G)
  定义体: sInf Finset.card '' { t : Finset G | K subseteq ⋃ g in t, (fun h => g * h) ⁻¹' V }

@[to_additive addIndex_empty]

Depends on / 依赖: Finset, Finset.card, subseteq
-/
noncomputable def index (K V : Set G) : Nat :=
sInf Finset.card '' { t : Finset G | K subseteq ⋃ g in t, (fun h => g * h) ⁻¹' V }

@[to_additive addIndex_empty]
/--
theorem `index_empty` / 定理 `index_empty`

English:
theorem index_empty
  given: {V : Set G}
  statement: index ∅ V = 0
  proof: by simp [index]

中文:
定理 index_empty
  条件: {V : Set G}
  结论: index ∅ V = 0
  证明: by simp [index]
-/
theorem index_empty {V : Set G} : index ∅ V = 0 := by simp [index]

variable [TopologicalSpace G]

/-- `prehaar K₀ U K` is a weighted version of the index, defined as `(K : U)/(K₀ : U)`.
  In the applications `K₀` is compact with non-empty interior, `U` is open containing `1`,
  and `K` is any compact set.
  The argument `K` is a (bundled) compact set, so that we can consider `prehaar K₀ U` as an
  element of `haarProduct` (below). -/
@[to_additive /-- additive version of `MeasureTheory.Measure.haar.prehaar` -/]
/--
Definition of `prehaar` / `prehaar` 的定义

English:
definition prehaar
  signature: (K₀ U : Set G) (K : Compacts G)
  body: (index (K : Set G) U : Real) / index K₀ U

@[to_additive]

中文:
定义 prehaar
  签名: (K₀ U : Set G) (K : Compacts G)
  定义体: (index (K : Set G) U : Real) / index K₀ U

@[to_additive]
-/
noncomputable def prehaar (K₀ U : Set G) (K : Compacts G) : Real :=
  (index (K : Set G) U : Real) / index K₀ U

@[to_additive]
/--
theorem `prehaar_empty` / 定理 `prehaar_empty`

English:
theorem prehaar_empty
  given: (K₀ : PositiveCompacts G) {U : Set G}
  statement: prehaar (K₀ : Set G) U ⊥ = 0
  proof: by
  rw [prehaar]; rw [Compacts.coe_bot]; rw [index_empty]; rw [Nat.cast_zero]; rw [zero_div]

@[to_additive]

中文:
定理 prehaar_empty
  条件: (K₀ : PositiveCompacts G) {U : Set G}
  结论: prehaar (K₀ : Set G) U ⊥ = 0
  证明: by
  rw [prehaar]; rw [Compacts.coe_bot]; rw [index_empty]; rw [Nat.cast_zero]; rw [zero_div]

@[to_additive]

Depends on / 依赖: Compacts, Compacts.coe_bot, Nat.cast_zero, cast_zero, coe_bot, index_empty, prehaar, zero_div
-/
theorem prehaar_empty (K₀ : PositiveCompacts G) {U : Set G} : prehaar (K₀ : Set G) U ⊥ = 0 := by
  rw [prehaar]; rw [Compacts.coe_bot]; rw [index_empty]; rw [Nat.cast_zero]; rw [zero_div]

@[to_additive]
/--
theorem `prehaar_nonneg` / 定理 `prehaar_nonneg`

English:
theorem prehaar_nonneg
  given: (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G)
  proof: by apply div_nonneg <;> norm_cast <;> apply zero_le

中文:
定理 prehaar_nonneg
  条件: (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G)
  证明: by apply div_nonneg <;> norm_cast <;> apply zero_le

Depends on / 依赖: div_nonneg, zero_le
-/
theorem prehaar_nonneg (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G) :
    0 <= prehaar (K₀ : Set G) U K := by apply div_nonneg <;> norm_cast <;> apply zero_le

/-- `haarProduct K₀` is the product of intervals `[0, (K : K₀)]`, for all compact sets `K`.
  For all `U`, we can show that `prehaar K₀ U ∈ haarProduct K₀`. -/
@[to_additive /-- additive version of `MeasureTheory.Measure.haar.haarProduct` -/]
/--
Definition of `haarProduct` / `haarProduct` 的定义

English:
definition haarProduct
  signature: (K₀ : Set G)
  body: pi univ fun K => Icc 0 index (K : Set G) K₀

@[to_additive (attr := simp)]

中文:
定义 haarProduct
  签名: (K₀ : Set G)
  定义体: pi univ fun K => Icc 0 index (K : Set G) K₀

@[to_additive (attr := simp)]
-/
def haarProduct (K₀ : Set G) : Set (Compacts G -> Real) :=
pi univ fun K => Icc 0 index (K : Set G) K₀

@[to_additive (attr := simp)]
/--
theorem `mem_prehaar_empty` / 定理 `mem_prehaar_empty`

English:
theorem mem_prehaar_empty
  given: {K₀ : Set G} {f : Compacts G -> Real}
  proof: by
  simp only [haarProduct, Set.pi, forall_prop_of_true, mem_univ, mem_ofPred_eq]

中文:
定理 mem_prehaar_empty
  条件: {K₀ : Set G} {f : Compacts G -> 实数}
  证明: by
  simp only [haarProduct, Set.pi, forall_prop_of_true, mem_univ, mem_ofPred_eq]

Depends on / 依赖: Set.pi, forall_prop_of_true, haarProduct, mem_ofPred_eq, mem_univ
-/
theorem mem_prehaar_empty {K₀ : Set G} {f : Compacts G -> Real} :
    f in haarProduct K₀ ↔ forall K : Compacts G, f K in Icc (0 : Real) (index (K : Set G) K₀) := by
  simp only [haarProduct, Set.pi, forall_prop_of_true, mem_univ, mem_ofPred_eq]

/-- The closure of the collection of elements of the form `prehaar K₀ U`,
  for `U` open neighbourhoods of `1`, contained in `V`. The closure is taken in the space
  `compacts G → ℝ`, with the topology of pointwise convergence.
  We show that the intersection of all these sets is nonempty, and the Haar measure
  on compact sets is defined to be an element in the closure of this intersection. -/
@[to_additive /-- additive version of `MeasureTheory.Measure.haar.clPrehaar` -/]
/--
Definition of `clPrehaar` / `clPrehaar` 的定义

English:
definition clPrehaar
  signature: (K₀ : Set G) (V : OpenNhdsOf (1 : G))
  body: closure prehaar K₀ '' { U : Set G | U subseteq V.1 ∧ IsOpen U ∧ (1 : G) in U }

中文:
定义 clPrehaar
  签名: (K₀ : Set G) (V : OpenNhdsOf (1 : G))
  定义体: closure prehaar K₀ '' { U : Set G | U subseteq V.1 ∧ IsOpen U ∧ (1 : G) in U }

Depends on / 依赖: IsOpen, closure, prehaar, subseteq
-/
def clPrehaar (K₀ : Set G) (V : OpenNhdsOf (1 : G)) : Set (Compacts G -> Real) :=
closure prehaar K₀ '' { U : Set G | U subseteq V.1 ∧ IsOpen U ∧ (1 : G) in U }

variable [IsTopologicalGroup G]

/-!
### Lemmas about `index`
-/


/-- If `K` is compact and `V` has nonempty interior, then the index `(K : V)` is well-defined,
  there is a finite set `t` satisfying the desired properties. -/
@[to_additive addIndex_defined
/-- If `K` is compact and `V` has nonempty interior, then the index `(K : V)` is well-defined,
  there is a finite set `t` satisfying the desired properties. -/]
/--
theorem `index_defined` / 定理 `index_defined`

English:
theorem index_defined
  given: {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty)
  proof: by
  rcases compact_covered_by_mul_left_translates hK hV with ⟨t, ht⟩; exact ⟨t.card, t, ht, rfl⟩

@[to_additive addIndex_elim]

中文:
定理 index_defined
  条件: {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty)
  证明: by
  rcases compact_covered_by_mul_left_translates hK hV with ⟨t, ht⟩; exact ⟨t.card, t, ht, rfl⟩

@[to_additive addIndex_elim]

Depends on / 依赖: compact_covered_by_mul_left_translates, t.card
-/
theorem index_defined {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty) :
    exists n : Nat, n in Finset.card '' { t : Finset G | K subseteq ⋃ g in t, (fun h => g * h) ⁻¹' V } := by
  rcases compact_covered_by_mul_left_translates hK hV with ⟨t, ht⟩; exact ⟨t.card, t, ht, rfl⟩

@[to_additive addIndex_elim]
/--
theorem `index_elim` / 定理 `index_elim`

English:
theorem index_elim
  given: {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty)
  proof: by
  have := Nat.sInf_mem (index_defined hK hV); rwa [mem_image] at this

@[to_additive le_addIndex_mul]

中文:
定理 index_elim
  条件: {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty)
  证明: by
  have := Nat.sInf_mem (index_defined hK hV); rwa [mem_image] at this

@[to_additive le_addIndex_mul]

Depends on / 依赖: Nat.sInf_mem, index_defined, mem_image, sInf_mem
-/
theorem index_elim {K V : Set G} (hK : IsCompact K) (hV : (interior V).Nonempty) :
    exists t : Finset G, (K subseteq ⋃ g in t, (fun h => g * h) ⁻¹' V) ∧ Finset.card t = index K V := by
  have := Nat.sInf_mem (index_defined hK hV); rwa [mem_image] at this

@[to_additive le_addIndex_mul]
/--
theorem `le_index_mul` / 定理 `le_index_mul`

English:
theorem le_index_mul
  statement: (K₀ : PositiveCompacts G) (K : Compacts G) {V : Set G}
  proof: by
  classical
  obtain ⟨s, h1s, h2s⟩ := index_elim K.isCompact K₀.interior_nonempty
  obtain ⟨t, h1t, h2t⟩ := index_elim K₀.isCompact hV
  rw [← h2s]; rw [← h2t]; rw [mul_comm]
  refine le_trans ?_ Finset.card_mul_le
  apply Nat.sInf_le; refine ⟨_, ?_, rfl⟩; rw [mem_ofPred_eq]; refine Subset.trans 

中文:
定理 le_index_mul
  结论: (K₀ : PositiveCompacts G) (K : Compacts G) {V : Set G}
  证明: by
  classical
  obtain ⟨s, h1s, h2s⟩ := index_elim K.isCompact K₀.interior_nonempty
  obtain ⟨t, h1t, h2t⟩ := index_elim K₀.isCompact hV
  rw [← h2s]; rw [← h2t]; rw [mul_comm]
  refine le_trans ?_ Finset.card_mul_le
  apply Nat.sInf_le; refine ⟨_, ?_, rfl⟩; rw [mem_ofPred_eq]; refine Subset.trans 

Depends on / 依赖: Finset, Finset.card_mul_le, K.isCompact, Nat.sInf_le, Subset, Subset.trans, card_mul_le, classical, index_elim, interior_nonempty, isCompact, le_trans, mem_biUnion, mem_ofPred_eq, mem_preimage, mul_assoc, mul_comm, preimage_subset_iff, sInf_le
-/
theorem le_index_mul (K₀ : PositiveCompacts G) (K : Compacts G) {V : Set G}
    (hV : (interior V).Nonempty) :
    index (K : Set G) V <= index (K : Set G) K₀ * index (K₀ : Set G) V := by
  classical
  obtain ⟨s, h1s, h2s⟩ := index_elim K.isCompact K₀.interior_nonempty
  obtain ⟨t, h1t, h2t⟩ := index_elim K₀.isCompact hV
  rw [← h2s]; rw [← h2t]; rw [mul_comm]
  refine le_trans ?_ Finset.card_mul_le
  apply Nat.sInf_le; refine ⟨_, ?_, rfl⟩; rw [mem_ofPred_eq]; refine Subset.trans h1s ?_
  apply iUnion₂_subset; intro g₁ hg₁; rw [preimage_subset_iff]; intro g₂ hg₂
  have := h1t hg₂
  rcases this with ⟨_, ⟨g₃, rfl⟩, A, ⟨hg₃, rfl⟩, h2V⟩; rw [mem_preimage, ← mul_assoc] at h2V
  exact mem_biUnion (Finset.mul_mem_mul hg₃ hg₁) h2V

set_option backward.isDefEq.respectTransparency false in
@[to_additive addIndex_pos]
/--
theorem `index_pos` / 定理 `index_pos`

English:
theorem index_pos
  given: (K : PositiveCompacts G) {V : Set G} (hV : (interior V).Nonempty)
  proof: by
  classical
  rw [index]; rw [Nat.sInf_def]; rw [Nat.find_pos]; rw [mem_image]
  · rintro ⟨t, h1t, h2t⟩; rw [Finset.card_eq_zero] at h2t; subst h2t
    obtain ⟨g, hg⟩ := K.interior_nonempty
    change g in (∅ : Set G)
    convert! h1t (interior_subset hg); symm
    simp only [Finset.notMem_empty,

中文:
定理 index_pos
  条件: (K : PositiveCompacts G) {V : Set G} (hV : (interior V).Nonempty)
  证明: by
  classical
  rw [index]; rw [Nat.sInf_def]; rw [Nat.find_pos]; rw [mem_image]
  · rintro ⟨t, h1t, h2t⟩; rw [Finset.card_eq_zero] at h2t; subst h2t
    obtain ⟨g, hg⟩ := K.interior_nonempty
    change g in (∅ : Set G)
    convert! h1t (interior_subset hg); symm
    simp only [Finset.notMem_empty,

Depends on / 依赖: Finset, Finset.card_eq_zero, Finset.notMem_empty, K.interior_nonempty, K.isCompact, Nat.find_pos, Nat.sInf_def, card_eq_zero, classical, convert, find_pos, iUnion_empty, iUnion_of_empty, index_defined, interior_nonempty, interior_subset, isCompact, mem_image, notMem_empty, sInf_def
-/
theorem index_pos (K : PositiveCompacts G) {V : Set G} (hV : (interior V).Nonempty) :
    0 < index (K : Set G) V := by
  classical
  rw [index]; rw [Nat.sInf_def]; rw [Nat.find_pos]; rw [mem_image]
  · rintro ⟨t, h1t, h2t⟩; rw [Finset.card_eq_zero] at h2t; subst h2t
    obtain ⟨g, hg⟩ := K.interior_nonempty
    change g in (∅ : Set G)
    convert! h1t (interior_subset hg); symm
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]
  · exact index_defined K.isCompact hV

@[to_additive addIndex_mono]
/--
theorem `index_mono` / 定理 `index_mono`

English:
theorem index_mono
  given: {K K' V : Set G} (hK' : IsCompact K') (h : K subseteq K') (hV : (interior V).Nonempty)
  proof: by
  rcases index_elim hK' hV with ⟨s, h1s, h2s⟩
  apply Nat.sInf_le; rw [mem_image]; exact ⟨s, Subset.trans h h1s, h2s⟩

@[to_additive addIndex_union_le]

中文:
定理 index_mono
  条件: {K K' V : Set G} (hK' : IsCompact K') (h : K subseteq K') (hV : (interior V).Nonempty)
  证明: by
  rcases index_elim hK' hV with ⟨s, h1s, h2s⟩
  apply Nat.sInf_le; rw [mem_image]; exact ⟨s, Subset.trans h h1s, h2s⟩

@[to_additive addIndex_union_le]

Depends on / 依赖: Nat.sInf_le, Subset, Subset.trans, index_elim, mem_image, sInf_le
-/
theorem index_mono {K K' V : Set G} (hK' : IsCompact K') (h : K subseteq K') (hV : (interior V).Nonempty) :
    index K V <= index K' V := by
  rcases index_elim hK' hV with ⟨s, h1s, h2s⟩
  apply Nat.sInf_le; rw [mem_image]; exact ⟨s, Subset.trans h h1s, h2s⟩

@[to_additive addIndex_union_le]
/--
theorem `index_union_le` / 定理 `index_union_le`

English:
theorem index_union_le
  given: (K₁ K₂ : Compacts G) {V : Set G} (hV : (interior V).Nonempty)
  proof: by
  classical
  rcases index_elim K₁.2 hV with ⟨s, h1s, h2s⟩
  rcases index_elim K₂.2 hV with ⟨t, h1t, h2t⟩
  rw [← h2s]; rw [← h2t]
  refine le_trans (Nat.sInf_le ⟨_, ?_, rfl⟩) (Finset.card_union_le _ _)
  rw [mem_ofPred_eq]; rw [Finset.set_biUnion_union]
  gcongr

@[to_additive addIndex_union_eq]

中文:
定理 index_union_le
  条件: (K₁ K₂ : Compacts G) {V : Set G} (hV : (interior V).Nonempty)
  证明: by
  classical
  rcases index_elim K₁.2 hV with ⟨s, h1s, h2s⟩
  rcases index_elim K₂.2 hV with ⟨t, h1t, h2t⟩
  rw [← h2s]; rw [← h2t]
  refine le_trans (Nat.sInf_le ⟨_, ?_, rfl⟩) (Finset.card_union_le _ _)
  rw [mem_ofPred_eq]; rw [Finset.set_biUnion_union]
  gcongr

@[to_additive addIndex_union_eq]

Depends on / 依赖: Finset, Finset.card_union_le, Finset.set_biUnion_union, Nat.sInf_le, card_union_le, classical, index_elim, le_trans, mem_ofPred_eq, sInf_le, set_biUnion_union
-/
theorem index_union_le (K₁ K₂ : Compacts G) {V : Set G} (hV : (interior V).Nonempty) :
    index (K₁.1 union K₂.1) V <= index K₁.1 V + index K₂.1 V := by
  classical
  rcases index_elim K₁.2 hV with ⟨s, h1s, h2s⟩
  rcases index_elim K₂.2 hV with ⟨t, h1t, h2t⟩
  rw [← h2s]; rw [← h2t]
  refine le_trans (Nat.sInf_le ⟨_, ?_, rfl⟩) (Finset.card_union_le _ _)
  rw [mem_ofPred_eq]; rw [Finset.set_biUnion_union]
  gcongr

@[to_additive addIndex_union_eq]
/--
theorem `index_union_eq` / 定理 `index_union_eq`

English:
theorem index_union_eq
  statement: (K₁ K₂ : Compacts G) {V : Set G} (hV : (interior V).Nonempty)
  proof: by
  classical
  apply le_antisymm (index_union_le K₁ K₂ hV)
  rcases index_elim (K₁.2.union K₂.2) hV with ⟨s, h1s, h2s⟩; rw [← h2s]
  have (K : Set G) (hK : K subseteq ⋃ g in s, (g * ·) ⁻¹' V) :
      index K V <= {g in s | ((g * ·) ⁻¹' V inter K).Nonempty}.card := by
    apply Nat.sInf_le; refine 

中文:
定理 index_union_eq
  结论: (K₁ K₂ : Compacts G) {V : Set G} (hV : (interior V).Nonempty)
  证明: by
  classical
  apply le_antisymm (index_union_le K₁ K₂ hV)
  rcases index_elim (K₁.2.union K₂.2) hV with ⟨s, h1s, h2s⟩; rw [← h2s]
  have (K : Set G) (hK : K subseteq ⋃ g in s, (g * ·) ⁻¹' V) :
      index K V <= {g in s | ((g * ·) ⁻¹' V inter K).Nonempty}.card := by
    apply Nat.sInf_le; refine 

Depends on / 依赖: Finset, Finset.mem_filter, Nat.sInf_le, Nonempty, classical, index_elim, index_union_le, le_antisymm, mem_filter, mem_iUnion, mem_ofPred_eq, mem_preimage, sInf_le, subseteq
-/
theorem index_union_eq (K₁ K₂ : Compacts G) {V : Set G} (hV : (interior V).Nonempty)
    (h : Disjoint (K₁.1 * V⁻¹) (K₂.1 * V⁻¹)) :
    index (K₁.1 union K₂.1) V = index K₁.1 V + index K₂.1 V := by
  classical
  apply le_antisymm (index_union_le K₁ K₂ hV)
  rcases index_elim (K₁.2.union K₂.2) hV with ⟨s, h1s, h2s⟩; rw [← h2s]
  have (K : Set G) (hK : K subseteq ⋃ g in s, (g * ·) ⁻¹' V) :
      index K V <= {g in s | ((g * ·) ⁻¹' V inter K).Nonempty}.card := by
    apply Nat.sInf_le; refine ⟨_, ?_, rfl⟩; rw [mem_ofPred_eq]
    intro g hg; rcases hK hg with ⟨_, ⟨g₀, rfl⟩, _, ⟨h1g₀, rfl⟩, h2g₀⟩
    simp only [mem_preimage] at h2g₀
    simp only [mem_iUnion]; use g₀; constructor; swap
    · simp only [Finset.mem_filter, h1g₀, true_and]; use g
      simp [hg, h2g₀]
    exact h2g₀
  refine
    le_trans
      (add_le_add (this K₁.1 <| Subset.trans subset_union_left h1s)
        (this K₂.1 <| Subset.trans subset_union_right h1s)) ?_
  rw [← Finset.card_union_of_disjoint]; rw [Finset.filter_union_right]
  · exact s.card_filter_le _
  apply Finset.disjoint_filter.mpr
  rintro g₁ _ ⟨g₂, h1g₂, h2g₂⟩ ⟨g₃, h1g₃, h2g₃⟩
  simp only [mem_preimage] at h1g₃ h1g₂
  refine h.le_bot (?_ : g₁⁻¹ in _)
  constructor <;> simp only [Set.mem_inv, Set.mem_mul]
  · refine ⟨_, h2g₂, (g₁ * g₂)⁻¹, ?_, ?_⟩
    · simp only [inv_inv, h1g₂]
    · simp only [mul_inv_rev, mul_inv_cancel_left]
  · refine ⟨_, h2g₃, (g₁ * g₃)⁻¹, ?_, ?_⟩
    · simp only [inv_inv, h1g₃]
    · simp only [mul_inv_rev, mul_inv_cancel_left]

@[to_additive add_left_addIndex_le]
/--
theorem `mul_left_index_le` / 定理 `mul_left_index_le`

English:
theorem mul_left_index_le
  statement: {K : Set G} (hK : IsCompact K) {V : Set G} (hV : (interior V).Nonempty)
  proof: by
  rcases index_elim hK hV with ⟨s, h1s, h2s⟩; rw [← h2s]
  apply Nat.sInf_le; rw [mem_image]
  refine ⟨s.map (Equiv.mulRight g⁻¹).toEmbedding, ?_, Finset.card_map _⟩
  simp only [mem_ofPred_eq]; refine Subset.trans (image_mono h1s) ?_
  rintro _ ⟨g₁, ⟨_, ⟨g₂, rfl⟩, ⟨_, ⟨hg₂, rfl⟩, hg₁⟩⟩, rfl⟩
  s

中文:
定理 mul_left_index_le
  结论: {K : Set G} (hK : IsCompact K) {V : Set G} (hV : (interior V).Nonempty)
  证明: by
  rcases index_elim hK hV with ⟨s, h1s, h2s⟩; rw [← h2s]
  apply Nat.sInf_le; rw [mem_image]
  refine ⟨s.map (Equiv.mulRight g⁻¹).toEmbedding, ?_, Finset.card_map _⟩
  simp only [mem_ofPred_eq]; refine Subset.trans (image_mono h1s) ?_
  rintro _ ⟨g₁, ⟨_, ⟨g₂, rfl⟩, ⟨_, ⟨hg₂, rfl⟩, hg₁⟩⟩, rfl⟩
  s

Depends on / 依赖: Equiv.coe_mulRight, Equiv.mulRight, Equiv.toEmbedding_apply, Finset, Finset.card_map, Finset.mem_map, Nat.sInf_le, Subset, Subset.trans, card_map, coe_mulRight, exists_exists_and_eq_and, exists_prop, image_mono, index_elim, mem_iUnion, mem_image, mem_map, mem_ofPred_eq, mem_preimage
-/
theorem mul_left_index_le {K : Set G} (hK : IsCompact K) {V : Set G} (hV : (interior V).Nonempty)
    (g : G) : index ((fun h => g * h) '' K) V <= index K V := by
  rcases index_elim hK hV with ⟨s, h1s, h2s⟩; rw [← h2s]
  apply Nat.sInf_le; rw [mem_image]
  refine ⟨s.map (Equiv.mulRight g⁻¹).toEmbedding, ?_, Finset.card_map _⟩
  simp only [mem_ofPred_eq]; refine Subset.trans (image_mono h1s) ?_
  rintro _ ⟨g₁, ⟨_, ⟨g₂, rfl⟩, ⟨_, ⟨hg₂, rfl⟩, hg₁⟩⟩, rfl⟩
  simp only [mem_preimage] at hg₁
  simp only [exists_prop, mem_iUnion, Finset.mem_map, Equiv.coe_mulRight,
    exists_exists_and_eq_and, mem_preimage, Equiv.toEmbedding_apply]
  refine ⟨_, hg₂, ?_⟩; simp only [mul_assoc, hg₁, inv_mul_cancel_left]

@[to_additive is_left_invariant_addIndex]
/--
theorem `is_left_invariant_index` / 定理 `is_left_invariant_index`

English:
theorem is_left_invariant_index
  statement: {K : Set G} (hK : IsCompact K) (g : G) {V : Set G}
  proof: by
  refine le_antisymm (mul_left_index_le hK hV g) ?_
  convert! mul_left_index_le (hK.image <| continuous_const_mul g) hV g⁻¹
  rw [image_image]
  simp

中文:
定理 is_left_invariant_index
  结论: {K : Set G} (hK : IsCompact K) (g : G) {V : Set G}
  证明: by
  refine le_antisymm (mul_left_index_le hK hV g) ?_
  convert! mul_left_index_le (hK.image <| continuous_const_mul g) hV g⁻¹
  rw [image_image]
  simp

Depends on / 依赖: continuous_const_mul, convert, hK.image, image_image, le_antisymm, mul_left_index_le
-/
theorem is_left_invariant_index {K : Set G} (hK : IsCompact K) (g : G) {V : Set G}
    (hV : (interior V).Nonempty) : index ((fun h => g * h) '' K) V = index K V := by
  refine le_antisymm (mul_left_index_le hK hV g) ?_
  convert! mul_left_index_le (hK.image <| continuous_const_mul g) hV g⁻¹
  rw [image_image]
  simp

/-!
### Lemmas about `prehaar`
-/


@[to_additive add_prehaar_le_addIndex]
/--
theorem `prehaar_le_index` / 定理 `prehaar_le_index`

English:
theorem prehaar_le_index
  statement: (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G)
  proof: by
  unfold prehaar; rw [div_le_iff₀] <;> norm_cast
  · apply le_index_mul K₀ K hU
  · exact index_pos K₀ hU

@[to_additive]

中文:
定理 prehaar_le_index
  结论: (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G)
  证明: by
  unfold prehaar; rw [div_le_iff₀] <;> norm_cast
  · apply le_index_mul K₀ K hU
  · exact index_pos K₀ hU

@[to_additive]

Depends on / 依赖: index_pos, le_index_mul, prehaar
-/
theorem prehaar_le_index (K₀ : PositiveCompacts G) {U : Set G} (K : Compacts G)
    (hU : (interior U).Nonempty) : prehaar (K₀ : Set G) U K <= index (K : Set G) K₀ := by
  unfold prehaar; rw [div_le_iff₀] <;> norm_cast
  · apply le_index_mul K₀ K hU
  · exact index_pos K₀ hU

@[to_additive]
/--
theorem `prehaar_pos` / 定理 `prehaar_pos`

English:
theorem prehaar_pos
  statement: (K₀ : PositiveCompacts G) {U : Set G} (hU : (interior U).Nonempty) {K : Set G}
  proof: by
  apply div_pos <;> norm_cast
  · apply index_pos ⟨⟨K, h1K⟩, h2K⟩ hU
  · exact index_pos K₀ hU

@[to_additive]

中文:
定理 prehaar_pos
  结论: (K₀ : PositiveCompacts G) {U : Set G} (hU : (interior U).Nonempty) {K : Set G}
  证明: by
  apply div_pos <;> norm_cast
  · apply index_pos ⟨⟨K, h1K⟩, h2K⟩ hU
  · exact index_pos K₀ hU

@[to_additive]

Depends on / 依赖: div_pos, index_pos
-/
theorem prehaar_pos (K₀ : PositiveCompacts G) {U : Set G} (hU : (interior U).Nonempty) {K : Set G}
    (h1K : IsCompact K) (h2K : (interior K).Nonempty) : 0 < prehaar (K₀ : Set G) U ⟨K, h1K⟩ := by
  apply div_pos <;> norm_cast
  · apply index_pos ⟨⟨K, h1K⟩, h2K⟩ hU
  · exact index_pos K₀ hU

@[to_additive]
/--
theorem `prehaar_mono` / 定理 `prehaar_mono`

English:
theorem prehaar_mono
  statement: {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty)
  proof: by
  simp only [prehaar]; rw [div_le_div_iff_of_pos_right]
  · exact mod_cast index_mono K₂.2 h hU
  · exact mod_cast index_pos K₀ hU

@[to_additive]

中文:
定理 prehaar_mono
  结论: {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty)
  证明: by
  simp only [prehaar]; rw [div_le_div_iff_of_pos_right]
  · exact mod_cast index_mono K₂.2 h hU
  · exact mod_cast index_pos K₀ hU

@[to_additive]

Depends on / 依赖: div_le_div_iff_of_pos_right, index_mono, index_pos, mod_cast, prehaar
-/
theorem prehaar_mono {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty)
    {K₁ K₂ : Compacts G} (h : (K₁ : Set G) subseteq K₂.1) :
    prehaar (K₀ : Set G) U K₁ <= prehaar (K₀ : Set G) U K₂ := by
  simp only [prehaar]; rw [div_le_div_iff_of_pos_right]
  · exact mod_cast index_mono K₂.2 h hU
  · exact mod_cast index_pos K₀ hU

@[to_additive]
/--
theorem `prehaar_self` / 定理 `prehaar_self`

English:
theorem prehaar_self
  given: {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty)
  proof: div_self ne_of_gt mod_cast index_pos K₀ hU

@[to_additive]

中文:
定理 prehaar_self
  条件: {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty)
  证明: div_self ne_of_gt mod_cast index_pos K₀ hU

@[to_additive]

Depends on / 依赖: div_self, index_pos, mod_cast, ne_of_gt
-/
theorem prehaar_self {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty) :
    prehaar (K₀ : Set G) U K₀.toCompacts = 1 :=
div_self ne_of_gt mod_cast index_pos K₀ hU

@[to_additive]
/--
theorem `prehaar_sup_le` / 定理 `prehaar_sup_le`

English:
theorem prehaar_sup_le
  statement: {K₀ : PositiveCompacts G} {U : Set G} (K₁ K₂ : Compacts G)
  proof: by
  simp only [prehaar]; rw [← add_div, div_le_div_iff_of_pos_right]
  · exact mod_cast index_union_le K₁ K₂ hU
  · exact mod_cast index_pos K₀ hU

@[to_additive]

中文:
定理 prehaar_sup_le
  结论: {K₀ : PositiveCompacts G} {U : Set G} (K₁ K₂ : Compacts G)
  证明: by
  simp only [prehaar]; rw [← add_div, div_le_div_iff_of_pos_right]
  · exact mod_cast index_union_le K₁ K₂ hU
  · exact mod_cast index_pos K₀ hU

@[to_additive]

Depends on / 依赖: add_div, div_le_div_iff_of_pos_right, index_pos, index_union_le, mod_cast, prehaar
-/
theorem prehaar_sup_le {K₀ : PositiveCompacts G} {U : Set G} (K₁ K₂ : Compacts G)
    (hU : (interior U).Nonempty) :
    prehaar (K₀ : Set G) U (K₁ ⊔ K₂) <= prehaar (K₀ : Set G) U K₁ + prehaar (K₀ : Set G) U K₂ := by
  simp only [prehaar]; rw [← add_div, div_le_div_iff_of_pos_right]
  · exact mod_cast index_union_le K₁ K₂ hU
  · exact mod_cast index_pos K₀ hU

@[to_additive]
/--
theorem `prehaar_sup_eq` / 定理 `prehaar_sup_eq`

English:
theorem prehaar_sup_eq
  statement: {K₀ : PositiveCompacts G} {U : Set G} {K₁ K₂ : Compacts G}
  proof: by
  simp only [prehaar]; rw [← add_div]
  -- Porting note: Here was `congr`, but `to_additive` failed to generate a theorem.
  refine congr_arg (fun x : Real => x / index K₀ U) ?_
  exact mod_cast index_union_eq K₁ K₂ hU h

@[to_additive]

中文:
定理 prehaar_sup_eq
  结论: {K₀ : PositiveCompacts G} {U : Set G} {K₁ K₂ : Compacts G}
  证明: by
  simp only [prehaar]; rw [← add_div]
  -- Porting note: Here was `congr`, but `to_additive` failed to generate a theorem.
  refine congr_arg (fun x : Real => x / index K₀ U) ?_
  exact mod_cast index_union_eq K₁ K₂ hU h

@[to_additive]

Depends on / 依赖: add_div, prehaar
-/
theorem prehaar_sup_eq {K₀ : PositiveCompacts G} {U : Set G} {K₁ K₂ : Compacts G}
    (hU : (interior U).Nonempty) (h : Disjoint (K₁.1 * U⁻¹) (K₂.1 * U⁻¹)) :
    prehaar (K₀ : Set G) U (K₁ ⊔ K₂) = prehaar (K₀ : Set G) U K₁ + prehaar (K₀ : Set G) U K₂ := by
  simp only [prehaar]; rw [← add_div]
  -- Porting note: Here was `congr`, but `to_additive` failed to generate a theorem.
  refine congr_arg (fun x : Real => x / index K₀ U) ?_
  exact mod_cast index_union_eq K₁ K₂ hU h

@[to_additive]
/--
theorem `is_left_invariant_prehaar` / 定理 `is_left_invariant_prehaar`

English:
theorem is_left_invariant_prehaar
  statement: {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty)
  proof: by
  simp only [prehaar, Compacts.coe_map, is_left_invariant_index K.isCompact _ hU]

中文:
定理 is_left_invariant_prehaar
  结论: {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty)
  证明: by
  simp only [prehaar, Compacts.coe_map, is_left_invariant_index K.isCompact _ hU]

Depends on / 依赖: Compacts, Compacts.coe_map, K.isCompact, coe_map, isCompact, is_left_invariant_index, prehaar
-/
theorem is_left_invariant_prehaar {K₀ : PositiveCompacts G} {U : Set G} (hU : (interior U).Nonempty)
    (g : G) (K : Compacts G) :
    prehaar (K₀ : Set G) U (K.map _ <| continuous_const_mul g) = prehaar (K₀ : Set G) U K := by
  simp only [prehaar, Compacts.coe_map, is_left_invariant_index K.isCompact _ hU]

/-!
### Lemmas about `haarProduct`
-/

@[to_additive]
/--
theorem `prehaar_mem_haarProduct` / 定理 `prehaar_mem_haarProduct`

English:
theorem prehaar_mem_haarProduct
  given: (K₀ : PositiveCompacts G) {U : Set G} (hU : (interior U).Nonempty)
  proof: by
    rintro ⟨K, hK⟩ _; rw [mem_Icc]; exact ⟨prehaar_nonneg K₀ _, prehaar_le_index K₀ _ hU⟩

@[to_additive]

中文:
定理 prehaar_mem_haarProduct
  条件: (K₀ : PositiveCompacts G) {U : Set G} (hU : (interior U).Nonempty)
  证明: by
    rintro ⟨K, hK⟩ _; rw [mem_Icc]; exact ⟨prehaar_nonneg K₀ _, prehaar_le_index K₀ _ hU⟩

@[to_additive]

Depends on / 依赖: mem_Icc, prehaar_le_index, prehaar_nonneg
-/
theorem prehaar_mem_haarProduct (K₀ : PositiveCompacts G) {U : Set G} (hU : (interior U).Nonempty) :
    prehaar (K₀ : Set G) U in haarProduct (K₀ : Set G) := by
    rintro ⟨K, hK⟩ _; rw [mem_Icc]; exact ⟨prehaar_nonneg K₀ _, prehaar_le_index K₀ _ hU⟩

@[to_additive]
/--
theorem `nonempty_iInter_clPrehaar` / 定理 `nonempty_iInter_clPrehaar`

English:
theorem nonempty_iInter_clPrehaar
  given: (K₀ : PositiveCompacts G)
  proof: by
  have : IsCompact (haarProduct (K₀ : Set G)) := by
    apply isCompact_univ_pi; intro K; apply isCompact_Icc
  refine this.inter_iInter_nonempty (clPrehaar K₀) (fun s => isClosed_closure) fun t => ?_
  let V₀ := ⋂ V in t, (V : OpenNhdsOf (1 : G)).carrier
have h1V₀ : IsOpen V₀ := isOpen_biInter_f

中文:
定理 nonempty_iInter_clPrehaar
  条件: (K₀ : PositiveCompacts G)
  证明: by
  have : IsCompact (haarProduct (K₀ : Set G)) := by
    apply isCompact_univ_pi; intro K; apply isCompact_Icc
  refine this.inter_iInter_nonempty (clPrehaar K₀) (fun s => isClosed_closure) fun t => ?_
  let V₀ := ⋂ V in t, (V : OpenNhdsOf (1 : G)).carrier
have h1V₀ : IsOpen V₀ := isOpen_biInter_f

Depends on / 依赖: IsCompact, IsOpen, OpenNhdsOf, carrier, clPrehaar, haarProduct, inter_iInter_nonempty, isClosed_closure, isCompact_Icc, isCompact_univ_pi, isOpen_biInter_finset, mem_iInter, prehaar, prehaar_mem_haarProduc, this.inter_iInter_nonempty
-/
theorem nonempty_iInter_clPrehaar (K₀ : PositiveCompacts G) :
    (haarProduct (K₀ : Set G) inter ⋂ V : OpenNhdsOf (1 : G), clPrehaar K₀ V).Nonempty := by
  have : IsCompact (haarProduct (K₀ : Set G)) := by
    apply isCompact_univ_pi; intro K; apply isCompact_Icc
  refine this.inter_iInter_nonempty (clPrehaar K₀) (fun s => isClosed_closure) fun t => ?_
  let V₀ := ⋂ V in t, (V : OpenNhdsOf (1 : G)).carrier
have h1V₀ : IsOpen V₀ := isOpen_biInter_finset by rintro ⟨⟨V, hV₁⟩, hV₂⟩ _; exact hV₁
  have h2V₀ : (1 : G) in V₀ := by simp only [V₀, mem_iInter]; rintro ⟨⟨V, hV₁⟩, hV₂⟩ _; exact hV₂
  refine ⟨prehaar K₀ V₀, ?_⟩
  constructor
  · apply prehaar_mem_haarProduct K₀; use 1; rwa [h1V₀.interior_eq]
  · simp only [mem_iInter]; rintro ⟨V, hV⟩ h2V; apply subset_closure
    apply mem_image_of_mem; rw [mem_ofPred_eq]
    exact ⟨Subset.trans (iInter_subset _ ⟨V, hV⟩) (iInter_subset _ h2V), h1V₀, h2V₀⟩

/-!
### Lemmas about `chaar`
-/

/-- This is the "limit" of `prehaar K₀ U K` as `U` becomes a smaller and smaller open
  neighborhood of `(1 : G)`. More precisely, it is defined to be an arbitrary element
  in the intersection of all the sets `clPrehaar K₀ V` in `haarProduct K₀`.
  This is roughly equal to the Haar measure on compact sets,
  but it can differ slightly. We do know that
  `haarMeasure K₀ (interior K) ≤ chaar K₀ K ≤ haarMeasure K₀ K`. -/
@[to_additive addCHaar /-- additive version of `MeasureTheory.Measure.haar.chaar` -/]
/--
Definition of `chaar` / `chaar` 的定义

English:
definition chaar
  signature: (K₀ : PositiveCompacts G) (K : Compacts G)
  body: Classical.choose (nonempty_iInter_clPrehaar K₀) K

@[to_additive addCHaar_mem_addHaarProduct]

中文:
定义 chaar
  签名: (K₀ : PositiveCompacts G) (K : Compacts G)
  定义体: Classical.choose (nonempty_iInter_clPrehaar K₀) K

@[to_additive addCHaar_mem_addHaarProduct]

Depends on / 依赖: Classical, Classical.choose, nonempty_iInter_clPrehaar
-/
noncomputable def chaar (K₀ : PositiveCompacts G) (K : Compacts G) : Real :=
  Classical.choose (nonempty_iInter_clPrehaar K₀) K

@[to_additive addCHaar_mem_addHaarProduct]
/--
theorem `chaar_mem_haarProduct` / 定理 `chaar_mem_haarProduct`

English:
theorem chaar_mem_haarProduct
  given: (K₀ : PositiveCompacts G)
  statement: chaar K₀ in haarProduct (K₀ : Set G)
  proof: (Classical.choose_spec (nonempty_iInter_clPrehaar K₀)).1

@[to_additive addCHaar_mem_clAddPrehaar]

中文:
定理 chaar_mem_haarProduct
  条件: (K₀ : PositiveCompacts G)
  结论: chaar K₀ in haarProduct (K₀ : Set G)
  证明: (Classical.choose_spec (nonempty_iInter_clPrehaar K₀)).1

@[to_additive addCHaar_mem_clAddPrehaar]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, nonempty_iInter_clPrehaar
-/
theorem chaar_mem_haarProduct (K₀ : PositiveCompacts G) : chaar K₀ in haarProduct (K₀ : Set G) :=
  (Classical.choose_spec (nonempty_iInter_clPrehaar K₀)).1

@[to_additive addCHaar_mem_clAddPrehaar]
/--
theorem `chaar_mem_clPrehaar` / 定理 `chaar_mem_clPrehaar`

English:
theorem chaar_mem_clPrehaar
  given: (K₀ : PositiveCompacts G) (V : OpenNhdsOf (1 : G))
  proof: by
  have := (Classical.choose_spec (nonempty_iInter_clPrehaar K₀)).2; rw [mem_iInter] at this
  exact this V

@[to_additive addCHaar_nonneg]

中文:
定理 chaar_mem_clPrehaar
  条件: (K₀ : PositiveCompacts G) (V : OpenNhdsOf (1 : G))
  证明: by
  have := (Classical.choose_spec (nonempty_iInter_clPrehaar K₀)).2; rw [mem_iInter] at this
  exact this V

@[to_additive addCHaar_nonneg]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, mem_iInter, nonempty_iInter_clPrehaar
-/
theorem chaar_mem_clPrehaar (K₀ : PositiveCompacts G) (V : OpenNhdsOf (1 : G)) :
    chaar K₀ in clPrehaar (K₀ : Set G) V := by
  have := (Classical.choose_spec (nonempty_iInter_clPrehaar K₀)).2; rw [mem_iInter] at this
  exact this V

@[to_additive addCHaar_nonneg]
/--
theorem `chaar_nonneg` / 定理 `chaar_nonneg`

English:
theorem chaar_nonneg
  given: (K₀ : PositiveCompacts G) (K : Compacts G)
  statement: 0 <= chaar K₀ K
  proof: by
  have := chaar_mem_haarProduct K₀ K (mem_univ _); rw [mem_Icc] at this; exact this.1

@[to_additive addCHaar_empty]

中文:
定理 chaar_nonneg
  条件: (K₀ : PositiveCompacts G) (K : Compacts G)
  结论: 0 <= chaar K₀ K
  证明: by
  have := chaar_mem_haarProduct K₀ K (mem_univ _); rw [mem_Icc] at this; exact this.1

@[to_additive addCHaar_empty]

Depends on / 依赖: chaar_mem_haarProduct, mem_Icc, mem_univ
-/
theorem chaar_nonneg (K₀ : PositiveCompacts G) (K : Compacts G) : 0 <= chaar K₀ K := by
  have := chaar_mem_haarProduct K₀ K (mem_univ _); rw [mem_Icc] at this; exact this.1

@[to_additive addCHaar_empty]
/--
theorem `chaar_empty` / 定理 `chaar_empty`

English:
theorem chaar_empty
  given: (K₀ : PositiveCompacts G)
  statement: chaar K₀ ⊥ = 0
  proof: by
  let eval : (Compacts G -> Real) -> Real := fun f => f ⊥
  have : Continuous eval := continuous_apply ⊥
  change chaar K₀ in eval ⁻¹' {(0 : Real)}
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, _, rfl⟩; apply prehaa

中文:
定理 chaar_empty
  条件: (K₀ : PositiveCompacts G)
  结论: chaar K₀ ⊥ = 0
  证明: by
  let eval : (Compacts G -> Real) -> Real := fun f => f ⊥
  have : Continuous eval := continuous_apply ⊥
  change chaar K₀ in eval ⁻¹' {(0 : Real)}
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, _, rfl⟩; apply prehaa

Depends on / 依赖: Compacts, Continuous, IsClosed, IsClosed.closure_subset_iff, chaar_mem_clPrehaar, clPrehaar, closure_subset_iff, continuous_apply, continuous_iff_isClosed, continuous_iff_isClosed.mp, isClosed_singleton, mem_of_subset_of_mem, prehaar_empty
-/
theorem chaar_empty (K₀ : PositiveCompacts G) : chaar K₀ ⊥ = 0 := by
  let eval : (Compacts G -> Real) -> Real := fun f => f ⊥
  have : Continuous eval := continuous_apply ⊥
  change chaar K₀ in eval ⁻¹' {(0 : Real)}
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, _, rfl⟩; apply prehaar_empty
  · apply continuous_iff_isClosed.mp this; exact isClosed_singleton

@[to_additive addCHaar_self]
/--
theorem `chaar_self` / 定理 `chaar_self`

English:
theorem chaar_self
  given: (K₀ : PositiveCompacts G)
  statement: chaar K₀ K₀.toCompacts = 1
  proof: by
  let eval : (Compacts G -> Real) -> Real := fun f => f K₀.toCompacts
  have : Continuous eval := continuous_apply _
  change chaar K₀ in eval ⁻¹' {(1 : Real)}
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨_, h2U, 

中文:
定理 chaar_self
  条件: (K₀ : PositiveCompacts G)
  结论: chaar K₀ K₀.toCompacts = 1
  证明: by
  let eval : (Compacts G -> Real) -> Real := fun f => f K₀.toCompacts
  have : Continuous eval := continuous_apply _
  change chaar K₀ in eval ⁻¹' {(1 : Real)}
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨_, h2U, 

Depends on / 依赖: Compacts, Continuous, IsClosed, IsClosed.closure_subset_iff, chaar_mem_clPrehaar, clPrehaar, closure_subset_iff, continuous_apply, continuous_iff_isClosed, continuous_iff_isClosed.mp, h2U.interior_eq, interior_eq, isClosed_singleton, mem_of_subset_of_mem, prehaar_self, toCompacts
-/
theorem chaar_self (K₀ : PositiveCompacts G) : chaar K₀ K₀.toCompacts = 1 := by
  let eval : (Compacts G -> Real) -> Real := fun f => f K₀.toCompacts
  have : Continuous eval := continuous_apply _
  change chaar K₀ in eval ⁻¹' {(1 : Real)}
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨_, h2U, h3U⟩, rfl⟩; apply prehaar_self
    rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_isClosed.mp this; exact isClosed_singleton

@[to_additive addCHaar_mono]
/--
theorem `chaar_mono` / 定理 `chaar_mono`

English:
theorem chaar_mono
  given: {K₀ : PositiveCompacts G} {K₁ K₂ : Compacts G} (h : (K₁ : Set G) subseteq K₂)
  proof: by
  let eval : (Compacts G -> Real) -> Real := fun f => f K₂ - f K₁
  have : Continuous eval := (continuous_apply K₂).sub (continuous_apply K₁)
  rw [← sub_nonneg]; change chaar K₀ in eval ⁻¹' Ici (0 : Real)
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.

中文:
定理 chaar_mono
  条件: {K₀ : PositiveCompacts G} {K₁ K₂ : Compacts G} (h : (K₁ : Set G) subseteq K₂)
  证明: by
  let eval : (Compacts G -> Real) -> Real := fun f => f K₂ - f K₁
  have : Continuous eval := (continuous_apply K₂).sub (continuous_apply K₁)
  rw [← sub_nonneg]; change chaar K₀ in eval ⁻¹' Ici (0 : Real)
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.

Depends on / 依赖: Compacts, Continuous, IsClosed, IsClosed.closure_subset_iff, chaar_mem_clPrehaar, clPrehaar, closure_subset_iff, continuous_apply, continuous_iff_isClosed, continuous_iff_isClosed.mp, h2U.interior_eq, interior_eq, mem_Ici, mem_of_subset_of_mem, mem_preimage, prehaar_mono, sub_nonneg
-/
theorem chaar_mono {K₀ : PositiveCompacts G} {K₁ K₂ : Compacts G} (h : (K₁ : Set G) subseteq K₂) :
    chaar K₀ K₁ <= chaar K₀ K₂ := by
  let eval : (Compacts G -> Real) -> Real := fun f => f K₂ - f K₁
  have : Continuous eval := (continuous_apply K₂).sub (continuous_apply K₁)
  rw [← sub_nonneg]; change chaar K₀ in eval ⁻¹' Ici (0 : Real)
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨_, h2U, h3U⟩, rfl⟩; simp only [eval, mem_preimage, mem_Ici, sub_nonneg]
    apply prehaar_mono _ h; rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_isClosed.mp this; exact isClosed_Ici

@[to_additive addCHaar_sup_le]
/--
theorem `chaar_sup_le` / 定理 `chaar_sup_le`

English:
theorem chaar_sup_le
  given: {K₀ : PositiveCompacts G} (K₁ K₂ : Compacts G)
  proof: by
  let eval : (Compacts G -> Real) -> Real := fun f => f K₁ + f K₂ - f (K₁ ⊔ K₂)
  have : Continuous eval := by
    exact ((continuous_apply K₁).add (continuous_apply K₂)).sub (continuous_apply (K₁ ⊔ K₂))
  rw [← sub_nonneg]; change chaar K₀ in eval ⁻¹' Ici (0 : Real)
  apply mem_of_subset_of_mem 

中文:
定理 chaar_sup_le
  条件: {K₀ : PositiveCompacts G} (K₁ K₂ : Compacts G)
  证明: by
  let eval : (Compacts G -> Real) -> Real := fun f => f K₁ + f K₂ - f (K₁ ⊔ K₂)
  have : Continuous eval := by
    exact ((continuous_apply K₁).add (continuous_apply K₂)).sub (continuous_apply (K₁ ⊔ K₂))
  rw [← sub_nonneg]; change chaar K₀ in eval ⁻¹' Ici (0 : Real)
  apply mem_of_subset_of_mem 

Depends on / 依赖: Compacts, Continuous, IsClosed, IsClosed.closure_subset_iff, chaar_mem_clPrehaar, clPrehaar, closure_subset_iff, continuous_apply, h2U.interior_eq, interior_eq, mem_Ici, mem_of_subset_of_mem, mem_preimage, prehaar_sup_le, sub_nonneg
-/
theorem chaar_sup_le {K₀ : PositiveCompacts G} (K₁ K₂ : Compacts G) :
    chaar K₀ (K₁ ⊔ K₂) <= chaar K₀ K₁ + chaar K₀ K₂ := by
  let eval : (Compacts G -> Real) -> Real := fun f => f K₁ + f K₂ - f (K₁ ⊔ K₂)
  have : Continuous eval := by
    exact ((continuous_apply K₁).add (continuous_apply K₂)).sub (continuous_apply (K₁ ⊔ K₂))
  rw [← sub_nonneg]; change chaar K₀ in eval ⁻¹' Ici (0 : Real)
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨_, h2U, h3U⟩, rfl⟩; simp only [eval, mem_preimage, mem_Ici, sub_nonneg]
    apply prehaar_sup_le; rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_isClosed.mp this; exact isClosed_Ici

@[to_additive addCHaar_sup_eq]
/--
theorem `chaar_sup_eq` / 定理 `chaar_sup_eq`

English:
theorem chaar_sup_eq
  statement: {K₀ : PositiveCompacts G}
  proof: by
  rcases SeparatedNhds.of_isCompact_isCompact_isClosed K₁.2 K₂.2 h₂ h
    with ⟨U₁, U₂, h1U₁, h1U₂, h2U₁, h2U₂, hU⟩
  rcases compact_open_separated_mul_right K₁.2 h1U₁ h2U₁ with ⟨L₁, h1L₁, h2L₁⟩
  rcases mem_nhds_iff.mp h1L₁ with ⟨V₁, h1V₁, h2V₁, h3V₁⟩
  replace h2L₁ := Subset.trans (mul_subset_m

中文:
定理 chaar_sup_eq
  结论: {K₀ : PositiveCompacts G}
  证明: by
  rcases SeparatedNhds.of_isCompact_isCompact_isClosed K₁.2 K₂.2 h₂ h
    with ⟨U₁, U₂, h1U₁, h1U₂, h2U₁, h2U₂, hU⟩
  rcases compact_open_separated_mul_right K₁.2 h1U₁ h2U₁ with ⟨L₁, h1L₁, h2L₁⟩
  rcases mem_nhds_iff.mp h1L₁ with ⟨V₁, h1V₁, h2V₁, h3V₁⟩
  replace h2L₁ := Subset.trans (mul_subset_m

Depends on / 依赖: SeparatedNhds, SeparatedNhds.of_isCompact_isCompact_isClosed, Subset, Subset.trans, compact_open_separated_mul_right, mem_nhds_iff, mem_nhds_iff.mp, mul_subset_mul_left, of_isCompact_isCompact_isClosed, replace
-/
theorem chaar_sup_eq {K₀ : PositiveCompacts G}
    {K₁ K₂ : Compacts G} (h : Disjoint K₁.1 K₂.1) (h₂ : IsClosed K₂.1) :
    chaar K₀ (K₁ ⊔ K₂) = chaar K₀ K₁ + chaar K₀ K₂ := by
  rcases SeparatedNhds.of_isCompact_isCompact_isClosed K₁.2 K₂.2 h₂ h
    with ⟨U₁, U₂, h1U₁, h1U₂, h2U₁, h2U₂, hU⟩
  rcases compact_open_separated_mul_right K₁.2 h1U₁ h2U₁ with ⟨L₁, h1L₁, h2L₁⟩
  rcases mem_nhds_iff.mp h1L₁ with ⟨V₁, h1V₁, h2V₁, h3V₁⟩
  replace h2L₁ := Subset.trans (mul_subset_mul_left h1V₁) h2L₁
  rcases compact_open_separated_mul_right K₂.2 h1U₂ h2U₂ with ⟨L₂, h1L₂, h2L₂⟩
  rcases mem_nhds_iff.mp h1L₂ with ⟨V₂, h1V₂, h2V₂, h3V₂⟩
  replace h2L₂ := Subset.trans (mul_subset_mul_left h1V₂) h2L₂
  let eval : (Compacts G -> Real) -> Real := fun f => f K₁ + f K₂ - f (K₁ ⊔ K₂)
  have : Continuous eval :=
    ((continuous_apply K₁).add (continuous_apply K₂)).sub (continuous_apply (K₁ ⊔ K₂))
  rw [eq_comm]; rw [← sub_eq_zero]; change chaar K₀ in eval ⁻¹' {(0 : Real)}
  let V := V₁ inter V₂
  apply
    mem_of_subset_of_mem _
      (chaar_mem_clPrehaar K₀
        ⟨⟨V⁻¹, (h2V₁.inter h2V₂).preimage continuous_inv⟩, by
          simp only [V, mem_inv, inv_one, h3V₁, h3V₂, mem_inter_iff, true_and]⟩)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨h1U, h2U, h3U⟩, rfl⟩
    simp only [eval, mem_preimage, sub_eq_zero, mem_singleton_iff]; rw [eq_comm]
    apply prehaar_sup_eq
    · rw [h2U.interior_eq]; exact ⟨1, h3U⟩
    · refine disjoint_of_subset ?_ ?_ hU
      · refine Subset.trans (mul_subset_mul Subset.rfl ?_) h2L₁
        exact Subset.trans (inv_subset.mpr h1U) inter_subset_left
      · refine Subset.trans (mul_subset_mul Subset.rfl ?_) h2L₂
        exact Subset.trans (inv_subset.mpr h1U) inter_subset_right
  · apply continuous_iff_isClosed.mp this; exact isClosed_singleton

@[to_additive is_left_invariant_addCHaar]
/--
theorem `is_left_invariant_chaar` / 定理 `is_left_invariant_chaar`

English:
theorem is_left_invariant_chaar
  given: {K₀ : PositiveCompacts G} (g : G) (K : Compacts G)
  proof: by
  let eval : (Compacts G -> Real) -> Real := fun f => f (K.map _ <| continuous_const_mul g) - f K
  have : Continuous eval := (continuous_apply (K.map _ _)).sub (continuous_apply K)
  rw [← sub_eq_zero]; change chaar K₀ in eval ⁻¹' {(0 : Real)}
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar 

中文:
定理 is_left_invariant_chaar
  条件: {K₀ : PositiveCompacts G} (g : G) (K : Compacts G)
  证明: by
  let eval : (Compacts G -> Real) -> Real := fun f => f (K.map _ <| continuous_const_mul g) - f K
  have : Continuous eval := (continuous_apply (K.map _ _)).sub (continuous_apply K)
  rw [← sub_eq_zero]; change chaar K₀ in eval ⁻¹' {(0 : Real)}
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar 

Depends on / 依赖: Compacts, Continuous, IsClosed, IsClosed.closure_subset_iff, K.map, chaar_mem_clPrehaar, clPrehaar, closure_subset_iff, continuous_apply, continuous_const_mul, h2U.interior_eq, interior_eq, is_left_invariant_prehaar, mem_of_subset_of_mem, mem_preimage, mem_singleton_iff, sub_eq_zero
-/
theorem is_left_invariant_chaar {K₀ : PositiveCompacts G} (g : G) (K : Compacts G) :
    chaar K₀ (K.map _ <| continuous_const_mul g) = chaar K₀ K := by
  let eval : (Compacts G -> Real) -> Real := fun f => f (K.map _ <| continuous_const_mul g) - f K
  have : Continuous eval := (continuous_apply (K.map _ _)).sub (continuous_apply K)
  rw [← sub_eq_zero]; change chaar K₀ in eval ⁻¹' {(0 : Real)}
  apply mem_of_subset_of_mem _ (chaar_mem_clPrehaar K₀ ⊤)
  unfold clPrehaar; rw [IsClosed.closure_subset_iff]
  · rintro _ ⟨U, ⟨_, h2U, h3U⟩, rfl⟩
    simp only [eval, mem_singleton_iff, mem_preimage, sub_eq_zero]
    apply is_left_invariant_prehaar; rw [h2U.interior_eq]; exact ⟨1, h3U⟩
  · apply continuous_iff_isClosed.mp this; exact isClosed_singleton

set_option backward.isDefEq.respectTransparency false in
/-- The function `chaar` interpreted in `ℝ≥0`, as a content -/
@[to_additive /-- additive version of `MeasureTheory.Measure.haar.haarContent` -/]
/--
Definition of `haarContent` / `haarContent` 的定义

English:
definition haarContent
  signature: (K₀ : PositiveCompacts G)
  body: ⟨chaar K₀ K, chaar_nonneg _ _⟩
  mono' K₁ K₂ h := by simp only [← NNReal.coe_le_coe, NNReal.toReal, chaar_mono, h]
  sup_disjoint' K₁ K₂ h _h₁ h₂ := by simp only [chaar_sup_eq h]; rfl
  sup_le' K₁ K₂ := by
    simp only [← NNReal.coe_le_coe, NNReal.coe_add]
    simp only [NNReal.toReal, chaar_sup_le

中文:
定义 haarContent
  签名: (K₀ : PositiveCompacts G)
  定义体: ⟨chaar K₀ K, chaar_nonneg _ _⟩
  mono' K₁ K₂ h := by simp only [← NNReal.coe_le_coe, NNReal.toReal, chaar_mono, h]
  sup_disjoint' K₁ K₂ h _h₁ h₂ := by simp only [chaar_sup_eq h]; rfl
  sup_le' K₁ K₂ := by
    simp only [← NNReal.coe_le_coe, NNReal.coe_add]
    simp only [NNReal.toReal, chaar_sup_le

Depends on / 依赖: chaar_nonneg
-/
noncomputable def haarContent (K₀ : PositiveCompacts G) : Content G where
  toFun K := ⟨chaar K₀ K, chaar_nonneg _ _⟩
  mono' K₁ K₂ h := by simp only [← NNReal.coe_le_coe, NNReal.toReal, chaar_mono, h]
  sup_disjoint' K₁ K₂ h _h₁ h₂ := by simp only [chaar_sup_eq h]; rfl
  sup_le' K₁ K₂ := by
    simp only [← NNReal.coe_le_coe, NNReal.coe_add]
    simp only [NNReal.toReal, chaar_sup_le]

/-! We only prove the properties for `haarContent` that we use at least twice below. -/


@[to_additive]
/--
theorem `haarContent_apply` / 定理 `haarContent_apply`

English:
theorem haarContent_apply
  given: (K₀ : PositiveCompacts G) (K : Compacts G)
  proof: rfl

中文:
定理 haarContent_apply
  条件: (K₀ : PositiveCompacts G) (K : Compacts G)
  证明: rfl
-/
theorem haarContent_apply (K₀ : PositiveCompacts G) (K : Compacts G) :
    haarContent K₀ K = show NNReal from ⟨chaar K₀ K, chaar_nonneg _ _⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The variant of `chaar_self` for `haarContent` -/
@[to_additive /-- The variant of `addCHaar_self` for `addHaarContent`. -/]
/--
theorem `haarContent_self` / 定理 `haarContent_self`

English:
theorem haarContent_self
  given: {K₀ : PositiveCompacts G}
  statement: haarContent K₀ K₀.toCompacts = 1
  proof: by
  simp_rw [← ENNReal.coe_one, haarContent_apply, ENNReal.coe_inj, chaar_self]; rfl

中文:
定理 haarContent_self
  条件: {K₀ : PositiveCompacts G}
  结论: haarContent K₀ K₀.toCompacts = 1
  证明: by
  simp_rw [← ENNReal.coe_one, haarContent_apply, ENNReal.coe_inj, chaar_self]; rfl

Depends on / 依赖: ENNReal, ENNReal.coe_inj, ENNReal.coe_one, chaar_self, coe_inj, coe_one, haarContent_apply, simp_rw
-/
theorem haarContent_self {K₀ : PositiveCompacts G} : haarContent K₀ K₀.toCompacts = 1 := by
  simp_rw [← ENNReal.coe_one, haarContent_apply, ENNReal.coe_inj, chaar_self]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The variant of `is_left_invariant_chaar` for `haarContent` -/
@[to_additive /-- The variant of `is_left_invariant_addCHaar` for `addHaarContent` -/]
/--
theorem `is_left_invariant_haarContent` / 定理 `is_left_invariant_haarContent`

English:
theorem is_left_invariant_haarContent
  given: {K₀ : PositiveCompacts G} (g : G) (K : Compacts G)
  proof: by
  simpa only [ENNReal.coe_inj, ← NNReal.coe_inj, haarContent_apply] using!
    is_left_invariant_chaar g K

@[to_additive]

中文:
定理 is_left_invariant_haarContent
  条件: {K₀ : PositiveCompacts G} (g : G) (K : Compacts G)
  证明: by
  simpa only [ENNReal.coe_inj, ← NNReal.coe_inj, haarContent_apply] using!
    is_left_invariant_chaar g K

@[to_additive]

Depends on / 依赖: ENNReal, ENNReal.coe_inj, NNReal, NNReal.coe_inj, coe_inj, haarContent_apply, is_left_invariant_chaar
-/
theorem is_left_invariant_haarContent {K₀ : PositiveCompacts G} (g : G) (K : Compacts G) :
    haarContent K₀ (K.map _ <| continuous_const_mul g) = haarContent K₀ K := by
  simpa only [ENNReal.coe_inj, ← NNReal.coe_inj, haarContent_apply] using!
    is_left_invariant_chaar g K

@[to_additive]
/--
theorem `haarContent_outerMeasure_self_pos` / 定理 `haarContent_outerMeasure_self_pos`

English:
theorem haarContent_outerMeasure_self_pos
  given: (K₀ : PositiveCompacts G)
  proof: by
  refine zero_lt_one.trans_le ?_
  rw [Content.outerMeasure_eq_iInf]
refine le_iInf₂ fun U hU => le_iInf fun hK₀ => le_trans ?_ le_iSup₂ K₀.toCompacts hK₀
  exact haarContent_self.ge

@[to_additive]

中文:
定理 haarContent_outerMeasure_self_pos
  条件: (K₀ : PositiveCompacts G)
  证明: by
  refine zero_lt_one.trans_le ?_
  rw [Content.outerMeasure_eq_iInf]
refine le_iInf₂ fun U hU => le_iInf fun hK₀ => le_trans ?_ le_iSup₂ K₀.toCompacts hK₀
  exact haarContent_self.ge

@[to_additive]

Depends on / 依赖: Content, Content.outerMeasure_eq_iInf, haarContent_self, haarContent_self.ge, le_iInf, le_trans, outerMeasure_eq_iInf, toCompacts, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem haarContent_outerMeasure_self_pos (K₀ : PositiveCompacts G) :
    0 < (haarContent K₀).outerMeasure K₀ := by
  refine zero_lt_one.trans_le ?_
  rw [Content.outerMeasure_eq_iInf]
refine le_iInf₂ fun U hU => le_iInf fun hK₀ => le_trans ?_ le_iSup₂ K₀.toCompacts hK₀
  exact haarContent_self.ge

@[to_additive]
/--
theorem `haarContent_outerMeasure_closure_pos` / 定理 `haarContent_outerMeasure_closure_pos`

English:
theorem haarContent_outerMeasure_closure_pos
  given: (K₀ : PositiveCompacts G)
  proof: (haarContent_outerMeasure_self_pos K₀).trans_le (OuterMeasure.mono _ subset_closure)

中文:
定理 haarContent_outerMeasure_closure_pos
  条件: (K₀ : PositiveCompacts G)
  证明: (haarContent_outerMeasure_self_pos K₀).trans_le (OuterMeasure.mono _ subset_closure)

Depends on / 依赖: OuterMeasure, OuterMeasure.mono, haarContent_outerMeasure_self_pos, subset_closure, trans_le
-/
theorem haarContent_outerMeasure_closure_pos (K₀ : PositiveCompacts G) :
    0 < (haarContent K₀).outerMeasure (closure K₀) :=
  (haarContent_outerMeasure_self_pos K₀).trans_le (OuterMeasure.mono _ subset_closure)

end haar

open haar

/-!
### The Haar measure
-/

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/-- The Haar measure on the locally compact group `G`, scaled so that `haarMeasure K₀ K₀ = 1`. -/
@[to_additive
/-- The Haar measure on the locally compact additive group `G`, scaled so that
`addHaarMeasure K₀ K₀ = 1`. -/]
/--
Definition of `haarMeasure` / `haarMeasure` 的定义

English:
definition haarMeasure
  signature: (K₀ : PositiveCompacts G)
  body: ((haarContent K₀).measure K₀)⁻¹ • (haarContent K₀).measure

@[to_additive]

中文:
定义 haarMeasure
  签名: (K₀ : PositiveCompacts G)
  定义体: ((haarContent K₀).measure K₀)⁻¹ • (haarContent K₀).measure

@[to_additive]

Depends on / 依赖: haarContent, measure
-/
noncomputable def haarMeasure (K₀ : PositiveCompacts G) : Measure G :=
  ((haarContent K₀).measure K₀)⁻¹ • (haarContent K₀).measure

@[to_additive]
/--
theorem `haarMeasure_apply` / 定理 `haarMeasure_apply`

English:
theorem haarMeasure_apply
  given: {K₀ : PositiveCompacts G} {s : Set G} (hs : MeasurableSet s)
  proof: by
  change ((haarContent K₀).measure K₀)⁻¹ * (haarContent K₀).measure s = _
  simp only [hs, div_eq_mul_inv, mul_comm, Content.measure_apply]

@[to_additive]

中文:
定理 haarMeasure_apply
  条件: {K₀ : PositiveCompacts G} {s : Set G} (hs : MeasurableSet s)
  证明: by
  change ((haarContent K₀).measure K₀)⁻¹ * (haarContent K₀).measure s = _
  simp only [hs, div_eq_mul_inv, mul_comm, Content.measure_apply]

@[to_additive]

Depends on / 依赖: Content, Content.measure_apply, div_eq_mul_inv, haarContent, measure, measure_apply, mul_comm
-/
theorem haarMeasure_apply {K₀ : PositiveCompacts G} {s : Set G} (hs : MeasurableSet s) :
    haarMeasure K₀ s = (haarContent K₀).outerMeasure s / (haarContent K₀).measure K₀ := by
  change ((haarContent K₀).measure K₀)⁻¹ * (haarContent K₀).measure s = _
  simp only [hs, div_eq_mul_inv, mul_comm, Content.measure_apply]

@[to_additive]
/--
Instance `isMulLeftInvariant_haarMeasure` / 实例 `isMulLeftInvariant_haarMeasure`

English:
instance isMulLeftInvariant_haarMeasure
  signature: (K₀ : PositiveCompacts G)
  body: by
  rw [← forall_measure_preimage_mul_iff]
  intro g A hA
  rw [haarMeasure_apply hA]; rw [haarMeasure_apply (measurable_const_mul g hA)]
  -- Porting note: Here was `congr 1`, but `to_additive` failed to generate a theorem.
  refine congr_arg (fun x : Real>=0∞ => x / (haarContent K₀).measure K₀) ?

中文:
实例 isMulLeftInvariant_haarMeasure
  签名: (K₀ : PositiveCompacts G)
  定义体: by
  rw [← forall_measure_preimage_mul_iff]
  intro g A hA
  rw [haarMeasure_apply hA]; rw [haarMeasure_apply (measurable_const_mul g hA)]
  -- Porting note: Here was `congr 1`, but `to_additive` failed to generate a theorem.
  refine congr_arg (fun x : Real>=0∞ => x / (haarContent K₀).measure K₀) ?

Depends on / 依赖: forall_measure_preimage_mul_iff, haarMeasure_apply, measurable_const_mul
-/
instance isMulLeftInvariant_haarMeasure (K₀ : PositiveCompacts G) :
    IsMulLeftInvariant (haarMeasure K₀) := by
  rw [← forall_measure_preimage_mul_iff]
  intro g A hA
  rw [haarMeasure_apply hA]; rw [haarMeasure_apply (measurable_const_mul g hA)]
  -- Porting note: Here was `congr 1`, but `to_additive` failed to generate a theorem.
  refine congr_arg (fun x : Real>=0∞ => x / (haarContent K₀).measure K₀) ?_
  apply Content.is_mul_left_invariant_outerMeasure
  apply is_left_invariant_haarContent

@[to_additive]
/--
theorem `haarMeasure_self` / 定理 `haarMeasure_self`

English:
theorem haarMeasure_self
  given: {K₀ : PositiveCompacts G}
  statement: haarMeasure K₀ K₀ = 1
  proof: by
  have : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group
  simp only [haarMeasure, coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [← K₀.isCompact.measure_closure]; rw [Content.measure_apply _ isClosed_closure.measurableSet]; rw [ENNReal.inv_mul_cancel]
  · exact (haarContent_outerMeasure_clo

中文:
定理 haarMeasure_self
  条件: {K₀ : PositiveCompacts G}
  结论: haarMeasure K₀ K₀ = 1
  证明: by
  have : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group
  simp only [haarMeasure, coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [← K₀.isCompact.measure_closure]; rw [Content.measure_apply _ isClosed_closure.measurableSet]; rw [ENNReal.inv_mul_cancel]
  · exact (haarContent_outerMeasure_clo

Depends on / 依赖: Content, Content.measure_apply, Content.outerMeasure_lt_top_of_isCompact, ENNReal, ENNReal.inv_mul_cancel, LocallyCompactSpace, Pi.smul_apply, closure, coe_smul, haarContent_outerMeasure_closure_pos, haarMeasure, inv_mul_cancel, isClosed_closure, isClosed_closure.measurableSet, isCompact, isCompact.closure, isCompact.measure_closure, locallyCompactSpace_of_group, measurableSet, measure_apply
-/
theorem haarMeasure_self {K₀ : PositiveCompacts G} : haarMeasure K₀ K₀ = 1 := by
  have : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group
  simp only [haarMeasure, coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [← K₀.isCompact.measure_closure]; rw [Content.measure_apply _ isClosed_closure.measurableSet]; rw [ENNReal.inv_mul_cancel]
  · exact (haarContent_outerMeasure_closure_pos K₀).ne'
  · exact (Content.outerMeasure_lt_top_of_isCompact _ K₀.isCompact.closure).ne

/-- The Haar measure is regular. -/
@[to_additive /-- The additive Haar measure is regular. -/]
/--
Instance `regular_haarMeasure` / 实例 `regular_haarMeasure`

English:
instance regular_haarMeasure
  signature: {K₀ : PositiveCompacts G}
  body: by
  have : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group
  apply Regular.smul
  rw [← K₀.isCompact.measure_closure]; rw [Content.measure_apply _ isClosed_closure.measurableSet]; rw [ENNReal.inv_ne_top]
  exact (haarContent_outerMeasure_closure_pos K₀).ne'

@[to_additive]

中文:
实例 regular_haarMeasure
  签名: {K₀ : PositiveCompacts G}
  定义体: by
  have : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group
  apply Regular.smul
  rw [← K₀.isCompact.measure_closure]; rw [Content.measure_apply _ isClosed_closure.measurableSet]; rw [ENNReal.inv_ne_top]
  exact (haarContent_outerMeasure_closure_pos K₀).ne'

@[to_additive]

Depends on / 依赖: Content, Content.measure_apply, ENNReal, ENNReal.inv_ne_top, LocallyCompactSpace, Regular, Regular.smul, haarContent_outerMeasure_closure_pos, inv_ne_top, isClosed_closure, isClosed_closure.measurableSet, isCompact, isCompact.measure_closure, locallyCompactSpace_of_group, measurableSet, measure_apply, measure_closure
-/
instance regular_haarMeasure {K₀ : PositiveCompacts G} : (haarMeasure K₀).Regular := by
  have : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group
  apply Regular.smul
  rw [← K₀.isCompact.measure_closure]; rw [Content.measure_apply _ isClosed_closure.measurableSet]; rw [ENNReal.inv_ne_top]
  exact (haarContent_outerMeasure_closure_pos K₀).ne'

@[to_additive]
/--
theorem `haarMeasure_closure_self` / 定理 `haarMeasure_closure_self`

English:
theorem haarMeasure_closure_self
  given: {K₀ : PositiveCompacts G}
  statement: haarMeasure K₀ (closure K₀) = 1
  proof: by
  rw [K₀.isCompact.measure_closure]; rw [haarMeasure_self]

中文:
定理 haarMeasure_closure_self
  条件: {K₀ : PositiveCompacts G}
  结论: haarMeasure K₀ (closure K₀) = 1
  证明: by
  rw [K₀.isCompact.measure_closure]; rw [haarMeasure_self]

Depends on / 依赖: haarMeasure_self, isCompact, isCompact.measure_closure, measure_closure
-/
theorem haarMeasure_closure_self {K₀ : PositiveCompacts G} : haarMeasure K₀ (closure K₀) = 1 := by
  rw [K₀.isCompact.measure_closure]; rw [haarMeasure_self]

/-- The Haar measure is sigma-finite in a second countable group. -/
@[to_additive /-- The additive Haar measure is sigma-finite in a second countable group. -/]
/--
Instance `sigmaFinite_haarMeasure` / 实例 `sigmaFinite_haarMeasure`

English:
instance sigmaFinite_haarMeasure
  signature: [SecondCountableTopology G] {K₀ : PositiveCompacts G}
  body: by
  have : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group; infer_instance

中文:
实例 sigmaFinite_haarMeasure
  签名: [SecondCountableTopology G] {K₀ : PositiveCompacts G}
  定义体: by
  have : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group; infer_instance

Depends on / 依赖: LocallyCompactSpace, infer_instance, locallyCompactSpace_of_group
-/
instance sigmaFinite_haarMeasure [SecondCountableTopology G] {K₀ : PositiveCompacts G} :
    SigmaFinite (haarMeasure K₀) := by
  have : LocallyCompactSpace G := K₀.locallyCompactSpace_of_group; infer_instance

/-- The Haar measure is a Haar measure, i.e., it is invariant and gives finite mass to compact
sets and positive mass to nonempty open sets. -/
@[to_additive
/-- The additive Haar measure is an additive Haar measure, i.e., it is invariant and gives finite
mass to compact sets and positive mass to nonempty open sets. -/]
/--
Instance `isHaarMeasure_haarMeasure` / 实例 `isHaarMeasure_haarMeasure`

English:
instance isHaarMeasure_haarMeasure
  signature: (K₀ : PositiveCompacts G)
  body: by
  apply
    isHaarMeasure_of_isCompact_nonempty_interior (haarMeasure K₀) K₀ K₀.isCompact
      K₀.interior_nonempty
  · simp only [haarMeasure_self]; exact one_ne_zero
  · simp only [haarMeasure_self, ne_eq, ENNReal.one_ne_top, not_false_eq_true]

中文:
实例 isHaarMeasure_haarMeasure
  签名: (K₀ : PositiveCompacts G)
  定义体: by
  apply
    isHaarMeasure_of_isCompact_nonempty_interior (haarMeasure K₀) K₀ K₀.isCompact
      K₀.interior_nonempty
  · simp only [haarMeasure_self]; exact one_ne_zero
  · simp only [haarMeasure_self, ne_eq, ENNReal.one_ne_top, not_false_eq_true]

Depends on / 依赖: ENNReal, ENNReal.one_ne_top, haarMeasure, haarMeasure_self, interior_nonempty, isCompact, isHaarMeasure_of_isCompact_nonempty_interior, ne_eq, not_false_eq_true, one_ne_top, one_ne_zero
-/
instance isHaarMeasure_haarMeasure (K₀ : PositiveCompacts G) : IsHaarMeasure (haarMeasure K₀) := by
  apply
    isHaarMeasure_of_isCompact_nonempty_interior (haarMeasure K₀) K₀ K₀.isCompact
      K₀.interior_nonempty
  · simp only [haarMeasure_self]; exact one_ne_zero
  · simp only [haarMeasure_self, ne_eq, ENNReal.one_ne_top, not_false_eq_true]

/-- `haar` is some choice of a Haar measure, on a locally compact group. -/
@[to_additive
/-- `addHaar` is some choice of a Haar measure, on a locally compact additive group. -/]
/--
Definition of `haar` / `haar` 的定义

English:
abbreviation haar
  signature: [LocallyCompactSpace G]
  body: haarMeasure Classical.arbitrary _

中文:
缩写 haar
  签名: [LocallyCompactSpace G]
  定义体: haarMeasure Classical.arbitrary _

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, haarMeasure
-/
noncomputable abbrev haar [LocallyCompactSpace G] : Measure G :=
haarMeasure Classical.arbitrary _

/-! Steinhaus theorem: if `E` has positive measure, then `E / E` contains a neighborhood of zero.
Note that this is not true for general regular Haar measures: in `ℝ × ℝ` where the first factor
has the discrete topology, then `E = ℝ × {0}` has infinite measure for the regular Haar measure,
but `E / E` does not contain a neighborhood of zero. On the other hand, it is always true for
inner regular Haar measures (and in particular for any Haar measure on a second countable group).
-/

open scoped Pointwise

@[to_additive]
/--
lemma `steinhaus_mul_aux` / 引理 `steinhaus_mul_aux`

English:
lemma steinhaus_mul_aux
  statement: (μ : Measure G) [IsHaarMeasure μ] [μ.InnerRegularCompactLTTop]
  proof: by
  /- For any measure `μ` and set `E` containing a compact set `K` of positive measure, there exists
  a neighborhood `V` of the identity such that `v • K \ K` has small measure for all `v ∈ V`, say
  `< μ K`. Then `v • K` and `K` cannot be disjoint, as otherwise `μ (v • K \ K) = μ (v • K) = μ K`.

中文:
引理 steinhaus_mul_aux
  结论: (μ : Measure G) [IsHaarMeasure μ] [μ.InnerRegularCompactLTTop]
  证明: by
  /- For any measure `μ` and set `E` containing a compact set `K` of positive measure, there exists
  a neighborhood `V` of the identity such that `v • K \ K` has small measure for all `v ∈ V`, say
  `< μ K`. Then `v • K` and `K` cannot be disjoint, as otherwise `μ (v • K \ K) = μ (v • K) = μ K`.
-/
private lemma steinhaus_mul_aux (μ : Measure G) [IsHaarMeasure μ] [μ.InnerRegularCompactLTTop]
    [LocallyCompactSpace G] (E : Set G) (hE : MeasurableSet E)
    (hEapprox : exists K subseteq E, IsCompact K ∧ 0 < μ K) : E / E in 𝓝 (1 : G) := by
  /- For any measure `μ` and set `E` containing a compact set `K` of positive measure, there exists
  a neighborhood `V` of the identity such that `v • K \ K` has small measure for all `v ∈ V`, say
  `< μ K`. Then `v • K` and `K` cannot be disjoint, as otherwise `μ (v • K \ K) = μ (v • K) = μ K`.
  This show that `K / K` contains the neighborhood `V` of `1`, and therefore that it is
  itself such a neighborhood. -/
  obtain ⟨K, hKE, hK, K_closed, hKpos⟩ : exists K subseteq E, IsCompact K ∧ IsClosed K ∧ 0 < μ K := by
    obtain ⟨K, hKE, hK_comp, hK_meas⟩ := hEapprox
    exact ⟨closure K, hK_comp.closure_subset_measurableSet hE hKE, hK_comp.closure,
      isClosed_closure, by rwa [hK_comp.measure_closure]⟩
  filter_upwards [eventually_nhds_one_measure_smul_sdiff_lt hK K_closed hKpos.ne' (μ := μ)]
    with g hg
  obtain ⟨_, ⟨x, hxK, rfl⟩, hgxK⟩ : exists x in g • K, x in K :=
     not_disjoint_iff.1 fun hd => by simp [hd.symm.sdiff_eq_right, measure_smul] at hg
  simpa using div_mem_div (hKE hgxK) (hKE hxK)

/-- **Steinhaus Theorem** for finite mass sets.

In any locally compact group `G` with a Haar measure `μ` that's inner regular on finite measure
sets, for any measurable set `E` of finite positive measure, the set `E / E` is a neighbourhood of
`1`. -/
@[to_additive
/-- **Steinhaus Theorem** for finite mass sets.

In any locally compact group `G` with a Haar measure `μ` that's inner regular on finite measure
sets, for any measurable set `E` of finite positive measure, the set `E - E` is a neighbourhood of
`0`. -/]
/--
theorem `div_mem_nhds_one_of_haar_pos_ne_top` / 定理 `div_mem_nhds_one_of_haar_pos_ne_top`

English:
theorem div_mem_nhds_one_of_haar_pos_ne_top
  statement: (μ : Measure G) [IsHaarMeasure μ]
  proof: steinhaus_mul_aux μ E hE hE.exists_lt_isCompact_of_ne_top hEfin hEpos

中文:
定理 div_mem_nhds_one_of_haar_pos_ne_top
  结论: (μ : Measure G) [IsHaarMeasure μ]
  证明: steinhaus_mul_aux μ E hE hE.exists_lt_isCompact_of_ne_top hEfin hEpos

Depends on / 依赖: exists_lt_isCompact_of_ne_top, hE.exists_lt_isCompact_of_ne_top, steinhaus_mul_aux
-/
theorem div_mem_nhds_one_of_haar_pos_ne_top (μ : Measure G) [IsHaarMeasure μ]
    [LocallyCompactSpace G] [μ.InnerRegularCompactLTTop] (E : Set G) (hE : MeasurableSet E)
    (hEpos : 0 < μ E) (hEfin : μ E != ∞) : E / E in 𝓝 (1 : G) :=
steinhaus_mul_aux μ E hE hE.exists_lt_isCompact_of_ne_top hEfin hEpos

/-- **Steinhaus Theorem**.

In any locally compact group `G` with an inner regular Haar measure `μ`,
for any measurable set `E` of positive measure, the set `E / E` is a neighbourhood of `1`. -/
@[to_additive
/-- **Steinhaus Theorem**.

In any locally compact group `G` with an inner regular Haar measure `μ`,
for any measurable set `E` of positive measure, the set `E - E` is a neighbourhood of `0`. -/]
/--
theorem `div_mem_nhds_one_of_haar_pos` / 定理 `div_mem_nhds_one_of_haar_pos`

English:
theorem div_mem_nhds_one_of_haar_pos
  statement: (μ : Measure G) [IsHaarMeasure μ] [LocallyCompactSpace G]
  proof: steinhaus_mul_aux μ E hE hE.exists_lt_isCompact hEpos

中文:
定理 div_mem_nhds_one_of_haar_pos
  结论: (μ : Measure G) [IsHaarMeasure μ] [LocallyCompactSpace G]
  证明: steinhaus_mul_aux μ E hE hE.exists_lt_isCompact hEpos

Depends on / 依赖: exists_lt_isCompact, hE.exists_lt_isCompact, steinhaus_mul_aux
-/
theorem div_mem_nhds_one_of_haar_pos (μ : Measure G) [IsHaarMeasure μ] [LocallyCompactSpace G]
    [InnerRegular μ] (E : Set G) (hE : MeasurableSet E) (hEpos : 0 < μ E) :
E / E in 𝓝 (1 : G) := steinhaus_mul_aux μ E hE hE.exists_lt_isCompact hEpos

section SecondCountable_SigmaFinite
/-! In this section, we investigate uniqueness of left-invariant measures without assuming that
the measure is finite on compact sets, but assuming σ-finiteness instead. We also rely on
second-countability, to ensure that the group operations are measurable: in this case, one can
bypass all topological arguments, and conclude using uniqueness of σ-finite left-invariant measures
in measurable groups.

For more general uniqueness statements without second-countability assumptions,
see the file `Mathlib/MeasureTheory/Measure/Haar/Unique.lean`.
-/

variable [SecondCountableTopology G]

/-- **Uniqueness of left-invariant measures**: In a second-countable locally compact group, any
  σ-finite left-invariant measure is a scalar multiple of the Haar measure.
  This is slightly weaker than assuming that `μ` is a Haar measure (in particular we don't require
  `μ ≠ 0`).
  See also `isMulLeftInvariant_eq_smul_of_regular`
  for a statement not assuming second-countability. -/
@[to_additive
/-- **Uniqueness of left-invariant measures**: In a second-countable locally compact additive group,
  any σ-finite left-invariant measure is a scalar multiple of the additive Haar measure.
  This is slightly weaker than assuming that `μ` is an additive Haar measure (in particular we don't
  require `μ ≠ 0`).
  See also `isAddLeftInvariant_eq_smul_of_regular`
  for a statement not assuming second-countability. -/]
/--
theorem `haarMeasure_unique` / 定理 `haarMeasure_unique`

English:
theorem haarMeasure_unique
  statement: (μ : Measure G) [SigmaFinite μ] [IsMulLeftInvariant μ]
  proof: by
  have A : Set.Nonempty (interior (closure (K₀ : Set G))) :=
    K₀.interior_nonempty.mono (interior_mono subset_closure)
  have := measure_eq_div_smul μ (haarMeasure K₀)
    (measure_pos_of_nonempty_interior _ A).ne' K₀.isCompact.closure.measure_ne_top
  rwa [haarMeasure_closure_self, div_one, K

中文:
定理 haarMeasure_unique
  结论: (μ : Measure G) [SigmaFinite μ] [IsMulLeftInvariant μ]
  证明: by
  have A : Set.Nonempty (interior (closure (K₀ : Set G))) :=
    K₀.interior_nonempty.mono (interior_mono subset_closure)
  have := measure_eq_div_smul μ (haarMeasure K₀)
    (measure_pos_of_nonempty_interior _ A).ne' K₀.isCompact.closure.measure_ne_top
  rwa [haarMeasure_closure_self, div_one, K

Depends on / 依赖: Nonempty, Set.Nonempty, closure, div_one, haarMeasure, haarMeasure_closure_self, interior, interior_mono, interior_nonempty, interior_nonempty.mono, isCompact, isCompact.closure.measure_ne_top, isCompact.measure_closure, measure_closure, measure_eq_div_smul, measure_ne_top, measure_pos_of_nonempty_interior, subset_closure
-/
theorem haarMeasure_unique (μ : Measure G) [SigmaFinite μ] [IsMulLeftInvariant μ]
    (K₀ : PositiveCompacts G) : μ = μ K₀ • haarMeasure K₀ := by
  have A : Set.Nonempty (interior (closure (K₀ : Set G))) :=
    K₀.interior_nonempty.mono (interior_mono subset_closure)
  have := measure_eq_div_smul μ (haarMeasure K₀)
    (measure_pos_of_nonempty_interior _ A).ne' K₀.isCompact.closure.measure_ne_top
  rwa [haarMeasure_closure_self, div_one, K₀.isCompact.measure_closure] at this

/-- Let `μ` be a σ-finite left invariant measure on `G`. Then `μ` is equal to the Haar measure
defined by `K₀` iff `μ K₀ = 1`. -/
@[to_additive /-- Let `μ` be a σ-finite left invariant measure on `G`. Then `μ` is equal to the
additive Haar measure defined by `K₀` iff `μ K₀ = 1`. -/]
/--
theorem `haarMeasure_eq_iff` / 定理 `haarMeasure_eq_iff`

English:
theorem haarMeasure_eq_iff
  statement: (K₀ : PositiveCompacts G) (μ : Measure G) [SigmaFinite μ]
  proof: ⟨fun h => h.symm ▸ haarMeasure_self, fun h => by rw [haarMeasure_unique μ K₀, h, one_smul]⟩

example [LocallyCompactSpace G] (μ : Measure G) [IsHaarMeasure μ] (K₀ : PositiveCompacts G) :
    μ = μ K₀.1 • haarMeasure K₀ :=
  haarMeasure_unique μ K₀

中文:
定理 haarMeasure_eq_iff
  结论: (K₀ : PositiveCompacts G) (μ : Measure G) [SigmaFinite μ]
  证明: ⟨fun h => h.symm ▸ haarMeasure_self, fun h => by rw [haarMeasure_unique μ K₀, h, one_smul]⟩

example [LocallyCompactSpace G] (μ : Measure G) [IsHaarMeasure μ] (K₀ : PositiveCompacts G) :
    μ = μ K₀.1 • haarMeasure K₀ :=
  haarMeasure_unique μ K₀

Depends on / 依赖: h.symm, haarMeasure_self, haarMeasure_unique, one_smul
-/
theorem haarMeasure_eq_iff (K₀ : PositiveCompacts G) (μ : Measure G) [SigmaFinite μ]
    [IsMulLeftInvariant μ] :
    haarMeasure K₀ = μ ↔ μ K₀ = 1 :=
  ⟨fun h => h.symm ▸ haarMeasure_self, fun h => by rw [haarMeasure_unique μ K₀, h, one_smul]⟩

example [LocallyCompactSpace G] (μ : Measure G) [IsHaarMeasure μ] (K₀ : PositiveCompacts G) :
    μ = μ K₀.1 • haarMeasure K₀ :=
  haarMeasure_unique μ K₀

/-- To show that an invariant σ-finite measure is regular it is sufficient to show that it is finite
  on some compact set with non-empty interior. -/
@[to_additive
/-- To show that an invariant σ-finite measure is regular it is sufficient to show that it is
  finite on some compact set with non-empty interior. -/]
/--
theorem `regular_of_isMulLeftInvariant` / 定理 `regular_of_isMulLeftInvariant`

English:
theorem regular_of_isMulLeftInvariant
  statement: {μ : Measure G} [SigmaFinite μ] [IsMulLeftInvariant μ]
  proof: by
  rw [haarMeasure_unique μ ⟨⟨K]; rw [hK⟩]; rw [h2K⟩]; exact Regular.smul hμK

中文:
定理 regular_of_isMulLeftInvariant
  结论: {μ : Measure G} [SigmaFinite μ] [IsMulLeftInvariant μ]
  证明: by
  rw [haarMeasure_unique μ ⟨⟨K]; rw [hK⟩]; rw [h2K⟩]; exact Regular.smul hμK

Depends on / 依赖: Regular, Regular.smul, haarMeasure_unique
-/
theorem regular_of_isMulLeftInvariant {μ : Measure G} [SigmaFinite μ] [IsMulLeftInvariant μ]
    {K : Set G} (hK : IsCompact K) (h2K : (interior K).Nonempty) (hμK : μ K != ∞) : Regular μ := by
  rw [haarMeasure_unique μ ⟨⟨K]; rw [hK⟩]; rw [h2K⟩]; exact Regular.smul hμK

end SecondCountable_SigmaFinite

end Group

end Measure

end MeasureTheory
