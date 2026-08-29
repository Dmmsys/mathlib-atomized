/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.GroupTheory.GroupAction.Pointwise
public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Von Neumann Boundedness

This file defines natural or von Neumann bounded sets and proves elementary properties.

## Main declarations

* `Bornology.IsVonNBounded`: A set `s` is von Neumann-bounded if every neighborhood of zero
  absorbs `s`.
* `Bornology.vonNBornology`: The bornology made of the von Neumann-bounded sets.

## Main results

* `Bornology.IsVonNBounded.of_topologicalSpace_le`: A coarser topology admits more
  von Neumann-bounded sets.
* `Bornology.IsVonNBounded.image`: A continuous linear image of a bounded set is bounded.
* `Bornology.isVonNBounded_iff_smul_tendsto_zero`: Given any sequence `ε` of scalars which tends
  to `𝓝[≠] 0`, we have that a set `S` is bounded if and only if for any sequence `x : ℕ → S`,
  `ε • x` tends to 0. This shows that bounded sets are completely determined by sequences, which is
  the key fact for proving that sequential continuity implies continuity for linear maps defined on
  a bornological space

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

-/

@[expose] public section


variable {𝕜 𝕜' E F ι : Type*}

open Set Filter Function
open scoped Topology Pointwise


namespace Bornology

section SeminormedRing

section Zero

variable (𝕜)
variable [SeminormedRing 𝕜] [SMul 𝕜 E] [Zero E]
variable [TopologicalSpace E]

/--
Definition of `IsVonNBounded` / `IsVonNBounded` 的定义

English:
definition IsVonNBounded
  signature: (s : Set E)
  body: forall ⦃V⦄, V in 𝓝 (0 : E) -> Absorbs 𝕜 V s

中文:
定义 IsVonNBounded
  签名: (s : Set E)
  定义体: forall ⦃V⦄, V in 𝓝 (0 : E) -> Absorbs 𝕜 V s

Depends on / 依赖: Absorbs
-/
def IsVonNBounded (s : Set E) : Prop :=
  forall ⦃V⦄, V in 𝓝 (0 : E) -> Absorbs 𝕜 V s

variable (E)

@[simp]
/--
theorem `isVonNBounded_empty` / 定理 `isVonNBounded_empty`

English:
theorem isVonNBounded_empty
  statement: IsVonNBounded 𝕜 (∅ : Set E)
  proof: fun _ _ => Absorbs.empty

中文:
定理 isVonNBounded_empty
  结论: IsVonNBounded 𝕜 (∅ : Set E)
  证明: fun _ _ => Absorbs.empty

Depends on / 依赖: Absorbs, Absorbs.empty
-/
theorem isVonNBounded_empty : IsVonNBounded 𝕜 (∅ : Set E) := fun _ _ => Absorbs.empty

variable {𝕜 E}

/--
theorem `isVonNBounded_iff` / 定理 `isVonNBounded_iff`

English:
theorem isVonNBounded_iff
  given: (s : Set E)
  statement: IsVonNBounded 𝕜 s ↔ forall V in 𝓝 (0 : E), Absorbs 𝕜 V s
  proof: Iff.rfl

中文:
定理 isVonNBounded_iff
  条件: (s : Set E)
  结论: IsVonNBounded 𝕜 s ↔ 对任意 V in 𝓝 (0 : E), Absorbs 𝕜 V s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isVonNBounded_iff (s : Set E) : IsVonNBounded 𝕜 s ↔ forall V in 𝓝 (0 : E), Absorbs 𝕜 V s :=
  Iff.rfl

/--
theorem `_root_.Filter.HasBasis.isVonNBounded_iff` / 定理 `_root_.Filter.HasBasis.isVonNBounded_iff`

English:
theorem _root_.Filter.HasBasis.isVonNBounded_iff
  statement: {q : ι -> Prop} {s : ι -> Set E} {A : Set E}
  proof: by
  refine ⟨fun hA i hi => hA (h.mem_of_mem hi), fun hA V hV => ?_⟩
  rcases h.mem_iff.mp hV with ⟨i, hi, hV⟩
  exact (hA i hi).mono_left hV

中文:
定理 _root_.Filter.HasBasis.isVonNBounded_iff
  结论: {q : ι -> 命题} {s : ι -> Set E} {A : Set E}
  证明: by
  refine ⟨fun hA i hi => hA (h.mem_of_mem hi), fun hA V hV => ?_⟩
  rcases h.mem_iff.mp hV with ⟨i, hi, hV⟩
  exact (hA i hi).mono_left hV

Depends on / 依赖: h.mem_iff.mp, h.mem_of_mem, mem_iff, mem_of_mem, mono_left
-/
theorem _root_.Filter.HasBasis.isVonNBounded_iff {q : ι -> Prop} {s : ι -> Set E} {A : Set E}
    (h : (𝓝 (0 : E)).HasBasis q s) : IsVonNBounded 𝕜 A ↔ forall i, q i -> Absorbs 𝕜 (s i) A := by
  refine ⟨fun hA i hi => hA (h.mem_of_mem hi), fun hA V hV => ?_⟩
  rcases h.mem_iff.mp hV with ⟨i, hi, hV⟩
  exact (hA i hi).mono_left hV

/--
theorem `IsVonNBounded.subset` / 定理 `IsVonNBounded.subset`

English:
theorem IsVonNBounded.subset
  given: {s₁ s₂ : Set E} (h : s₁ subseteq s₂) (hs₂ : IsVonNBounded 𝕜 s₂)
  proof: fun _ hV => (hs₂ hV).mono_right h

@[simp]

中文:
定理 IsVonNBounded.subset
  条件: {s₁ s₂ : Set E} (h : s₁ subseteq s₂) (hs₂ : IsVonNBounded 𝕜 s₂)
  证明: fun _ hV => (hs₂ hV).mono_right h

@[simp]

Depends on / 依赖: mono_right
-/
theorem IsVonNBounded.subset {s₁ s₂ : Set E} (h : s₁ subseteq s₂) (hs₂ : IsVonNBounded 𝕜 s₂) :
    IsVonNBounded 𝕜 s₁ := fun _ hV => (hs₂ hV).mono_right h

@[simp]
/--
theorem `isVonNBounded_union` / 定理 `isVonNBounded_union`

English:
theorem isVonNBounded_union
  given: {s t : Set E}
  proof: by
  simp only [IsVonNBounded, absorbs_union, forall_and]

中文:
定理 isVonNBounded_union
  条件: {s t : Set E}
  证明: by
  simp only [IsVonNBounded, absorbs_union, forall_and]

Depends on / 依赖: IsVonNBounded, absorbs_union, forall_and
-/
theorem isVonNBounded_union {s t : Set E} :
    IsVonNBounded 𝕜 (s union t) ↔ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t := by
  simp only [IsVonNBounded, absorbs_union, forall_and]

/--
theorem `IsVonNBounded.union` / 定理 `IsVonNBounded.union`

English:
theorem IsVonNBounded.union
  given: {s₁ s₂ : Set E} (hs₁ : IsVonNBounded 𝕜 s₁) (hs₂ : IsVonNBounded 𝕜 s₂)
  proof: isVonNBounded_union.2 ⟨hs₁, hs₂⟩

@[nontriviality]

中文:
定理 IsVonNBounded.union
  条件: {s₁ s₂ : Set E} (hs₁ : IsVonNBounded 𝕜 s₁) (hs₂ : IsVonNBounded 𝕜 s₂)
  证明: isVonNBounded_union.2 ⟨hs₁, hs₂⟩

@[nontriviality]

Depends on / 依赖: isVonNBounded_union
-/
theorem IsVonNBounded.union {s₁ s₂ : Set E} (hs₁ : IsVonNBounded 𝕜 s₁) (hs₂ : IsVonNBounded 𝕜 s₂) :
    IsVonNBounded 𝕜 (s₁ union s₂) := isVonNBounded_union.2 ⟨hs₁, hs₂⟩

@[nontriviality]
/--
theorem `IsVonNBounded.of_boundedSpace` / 定理 `IsVonNBounded.of_boundedSpace`

English:
theorem IsVonNBounded.of_boundedSpace
  given: [BoundedSpace 𝕜] {s : Set E}
  statement: IsVonNBounded 𝕜 s
  proof: fun _ _ =>
  .of_boundedSpace

@[nontriviality]

中文:
定理 IsVonNBounded.of_boundedSpace
  条件: [BoundedSpace 𝕜] {s : Set E}
  结论: IsVonNBounded 𝕜 s
  证明: fun _ _ =>
  .of_boundedSpace

@[nontriviality]

Depends on / 依赖: SeminormedRing, SeminormedRing.toNonUnitalSeminormedRing, toNonUnitalSeminormedRing
-/
theorem IsVonNBounded.of_boundedSpace [BoundedSpace 𝕜] {s : Set E} : IsVonNBounded 𝕜 s := fun _ _ =>
  .of_boundedSpace

@[nontriviality]
/--
theorem `IsVonNBounded.of_subsingleton` / 定理 `IsVonNBounded.of_subsingleton`

English:
theorem IsVonNBounded.of_subsingleton
  given: [Subsingleton E] {s : Set E}
  statement: IsVonNBounded 𝕜 s
  proof: fun U hU => .of_forall fun c => calc
    s subseteq univ := subset_univ s
_ = c • U := .symm Subsingleton.eq_univ_of_nonempty (Filter.nonempty_of_mem hU).image _

@[simp]

中文:
定理 IsVonNBounded.of_subsingleton
  条件: [Subsingleton E] {s : Set E}
  结论: IsVonNBounded 𝕜 s
  证明: fun U hU => .of_forall fun c => calc
    s subseteq univ := subset_univ s
_ = c • U := .symm Subsingleton.eq_univ_of_nonempty (Filter.nonempty_of_mem hU).image _

@[simp]

Depends on / 依赖: Filter, Filter.nonempty_of_mem, NonUnitalNormedRing, NonUnitalNormedRing.toNonUnitalSeminormedRing, Subsingleton, Subsingleton.eq_univ_of_nonempty, eq_univ_of_nonempty, nonempty_of_mem, of_forall, subset_univ, subseteq, toNonUnitalSeminormedRing
-/
theorem IsVonNBounded.of_subsingleton [Subsingleton E] {s : Set E} : IsVonNBounded 𝕜 s :=
  fun U hU => .of_forall fun c => calc
    s subseteq univ := subset_univ s
_ = c • U := .symm Subsingleton.eq_univ_of_nonempty (Filter.nonempty_of_mem hU).image _

@[simp]
/--
theorem `isVonNBounded_iUnion` / 定理 `isVonNBounded_iUnion`

English:
theorem isVonNBounded_iUnion
  given: {ι : Sort*} [Finite ι] {s : ι -> Set E}
  proof: by
  simp only [IsVonNBounded, absorbs_iUnion, @forall_comm ι]

中文:
定理 isVonNBounded_iUnion
  条件: {ι : Sort*} [Finite ι] {s : ι -> Set E}
  证明: by
  simp only [IsVonNBounded, absorbs_iUnion, @forall_comm ι]

Depends on / 依赖: IsVonNBounded, NormedRing, NormedRing.toSeminormedRing, SeminormedRing, absorbs_iUnion, forall_comm, toSeminormedRing
-/
theorem isVonNBounded_iUnion {ι : Sort*} [Finite ι] {s : ι -> Set E} :
    IsVonNBounded 𝕜 (⋃ i, s i) ↔ forall i, IsVonNBounded 𝕜 (s i) := by
  simp only [IsVonNBounded, absorbs_iUnion, @forall_comm ι]

/--
theorem `isVonNBounded_biUnion` / 定理 `isVonNBounded_biUnion`

English:
theorem isVonNBounded_biUnion
  given: {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι -> Set E}
  proof: by
  have _ := hI.to_subtype
  rw [biUnion_eq_iUnion]; rw [isVonNBounded_iUnion]; rw [Subtype.forall]

中文:
定理 isVonNBounded_biUnion
  条件: {ι : 类型} {I : Set ι} (hI : I.Finite) {s : ι -> Set E}
  证明: by
  have _ := hI.to_subtype
  rw [biUnion_eq_iUnion]; rw [isVonNBounded_iUnion]; rw [Subtype.forall]

Depends on / 依赖: NormedRing, NormedRing.toNonUnitalNormedRing, Subtype, Subtype.forall, biUnion_eq_iUnion, hI.to_subtype, isVonNBounded_iUnion, toNonUnitalNormedRing, to_subtype
-/
theorem isVonNBounded_biUnion {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι -> Set E} :
    IsVonNBounded 𝕜 (⋃ i in I, s i) ↔ forall i in I, IsVonNBounded 𝕜 (s i) := by
  have _ := hI.to_subtype
  rw [biUnion_eq_iUnion]; rw [isVonNBounded_iUnion]; rw [Subtype.forall]

/--
theorem `isVonNBounded_sUnion` / 定理 `isVonNBounded_sUnion`

English:
theorem isVonNBounded_sUnion
  given: {S : Set (Set E)} (hS : S.Finite)
  proof: by
  rw [sUnion_eq_biUnion]; rw [isVonNBounded_biUnion hS]

中文:
定理 isVonNBounded_sUnion
  条件: {S : Set (Set E)} (hS : S.Finite)
  证明: by
  rw [sUnion_eq_biUnion]; rw [isVonNBounded_biUnion hS]

Depends on / 依赖: NonUnitalNormedCommRing, NonUnitalNormedCommRing.toNonUnitalSeminormedCommRing, isVonNBounded_biUnion, sUnion_eq_biUnion, toNonUnitalSeminormedCommRing
-/
theorem isVonNBounded_sUnion {S : Set (Set E)} (hS : S.Finite) :
    IsVonNBounded 𝕜 (⋃₀ S) ↔ forall s in S, IsVonNBounded 𝕜 s := by
  rw [sUnion_eq_biUnion]; rw [isVonNBounded_biUnion hS]

end Zero

section ContinuousAdd

variable [SeminormedRing 𝕜] [AddZeroClass E] [TopologicalSpace E] [ContinuousAdd E]
  [DistribSMul 𝕜 E] {s t : Set E}

/--
theorem `IsVonNBounded.add` / 定理 `IsVonNBounded.add`

English:
theorem IsVonNBounded.add
  given: (hs : IsVonNBounded 𝕜 s) (ht : IsVonNBounded 𝕜 t)
  proof: fun U hU => by
  rcases exists_open_nhds_zero_add_subset hU with ⟨V, hVo, hV, hVU⟩
  exact ((hs <| hVo.mem_nhds hV).add (ht <| hVo.mem_nhds hV)).mono_left hVU

中文:
定理 IsVonNBounded.add
  条件: (hs : IsVonNBounded 𝕜 s) (ht : IsVonNBounded 𝕜 t)
  证明: fun U hU => by
  rcases exists_open_nhds_zero_add_subset hU with ⟨V, hVo, hV, hVU⟩
  exact ((hs <| hVo.mem_nhds hV).add (ht <| hVo.mem_nhds hV)).mono_left hVU

Depends on / 依赖: SeminormedCommRing, SeminormedCommRing.toNonUnitalSeminormedCommRing, toNonUnitalSeminormedCommRing
-/
protected theorem IsVonNBounded.add (hs : IsVonNBounded 𝕜 s) (ht : IsVonNBounded 𝕜 t) :
    IsVonNBounded 𝕜 (s + t) := fun U hU => by
  rcases exists_open_nhds_zero_add_subset hU with ⟨V, hVo, hV, hVU⟩
  exact ((hs <| hVo.mem_nhds hV).add (ht <| hVo.mem_nhds hV)).mono_left hVU

end ContinuousAdd

section IsTopologicalAddGroup

variable [SeminormedRing 𝕜] [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [DistribMulAction 𝕜 E] {s t : Set E}

/--
theorem `IsVonNBounded.neg` / 定理 `IsVonNBounded.neg`

English:
theorem IsVonNBounded.neg
  given: (hs : IsVonNBounded 𝕜 s)
  statement: IsVonNBounded 𝕜 (-s)
  proof: fun U hU => by
  rw [← neg_neg U]
  exact (hs <| neg_mem_nhds_zero _ hU).neg_neg

@[simp]

中文:
定理 IsVonNBounded.neg
  条件: (hs : IsVonNBounded 𝕜 s)
  结论: IsVonNBounded 𝕜 (-s)
  证明: fun U hU => by
  rw [← neg_neg U]
  exact (hs <| neg_mem_nhds_zero _ hU).neg_neg

@[simp]

Depends on / 依赖: NormedCommRing, NormedCommRing.toNonUnitalNormedCommRing, toNonUnitalNormedCommRing
-/
protected theorem IsVonNBounded.neg (hs : IsVonNBounded 𝕜 s) : IsVonNBounded 𝕜 (-s) := fun U hU => by
  rw [← neg_neg U]
  exact (hs <| neg_mem_nhds_zero _ hU).neg_neg

@[simp]
/--
theorem `isVonNBounded_neg` / 定理 `isVonNBounded_neg`

English:
theorem isVonNBounded_neg
  statement: IsVonNBounded 𝕜 (-s) ↔ IsVonNBounded 𝕜 s
  proof: ⟨fun h => neg_neg s ▸ h.neg, fun h => h.neg⟩

alias ⟨IsVonNBounded.of_neg, _⟩ := isVonNBounded_neg

中文:
定理 isVonNBounded_neg
  结论: IsVonNBounded 𝕜 (-s) ↔ IsVonNBounded 𝕜 s
  证明: ⟨fun h => neg_neg s ▸ h.neg, fun h => h.neg⟩

alias ⟨IsVonNBounded.of_neg, _⟩ := isVonNBounded_neg

Depends on / 依赖: NormedCommRing, NormedCommRing.toSeminormedCommRing, h.neg, neg_neg, toSeminormedCommRing
-/
theorem isVonNBounded_neg : IsVonNBounded 𝕜 (-s) ↔ IsVonNBounded 𝕜 s :=
  ⟨fun h => neg_neg s ▸ h.neg, fun h => h.neg⟩

alias ⟨IsVonNBounded.of_neg, _⟩ := isVonNBounded_neg

/--
theorem `IsVonNBounded.sub` / 定理 `IsVonNBounded.sub`

English:
theorem IsVonNBounded.sub
  given: (hs : IsVonNBounded 𝕜 s) (ht : IsVonNBounded 𝕜 t)
  proof: by
  rw [sub_eq_add_neg]
  exact hs.add ht.neg

中文:
定理 IsVonNBounded.sub
  条件: (hs : IsVonNBounded 𝕜 s) (ht : IsVonNBounded 𝕜 t)
  证明: by
  rw [sub_eq_add_neg]
  exact hs.add ht.neg
-/
protected theorem IsVonNBounded.sub (hs : IsVonNBounded 𝕜 s) (ht : IsVonNBounded 𝕜 t) :
    IsVonNBounded 𝕜 (s - t) := by
  rw [sub_eq_add_neg]
  exact hs.add ht.neg

end IsTopologicalAddGroup

end SeminormedRing

section MultipleTopologies

variable [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

/--
theorem `IsVonNBounded.of_topologicalSpace_le` / 定理 `IsVonNBounded.of_topologicalSpace_le`

English:
theorem IsVonNBounded.of_topologicalSpace_le
  statement: {t t' : TopologicalSpace E} (h : t <= t') {s : Set E}
  proof: fun _ hV =>
hs (le_iff_nhds t t').mp h 0 hV

中文:
定理 IsVonNBounded.of_topologicalSpace_le
  结论: {t t' : TopologicalSpace E} (h : t <= t') {s : Set E}
  证明: fun _ hV =>
hs (le_iff_nhds t t').mp h 0 hV
-/
theorem IsVonNBounded.of_topologicalSpace_le {t t' : TopologicalSpace E} (h : t <= t') {s : Set E}
    (hs : @IsVonNBounded 𝕜 E _ _ _ t s) : @IsVonNBounded 𝕜 E _ _ _ t' s := fun _ hV =>
hs (le_iff_nhds t t').mp h 0 hV

end MultipleTopologies

/--
lemma `isVonNBounded_iff_tendsto_smallSets_nhds` / 引理 `isVonNBounded_iff_tendsto_smallSets_nhds`

English:
lemma isVonNBounded_iff_tendsto_smallSets_nhds
  statement: {𝕜 E : Type*} [NormedDivisionRing 𝕜]
  proof: by
  rw [tendsto_smallSets_iff]
  refine forall₂_congr fun V hV => ?_
  simp only [absorbs_iff_eventually_nhds_zero (mem_of_mem_nhds hV), mapsTo_iff_image_subset,
    image_smul]

alias ⟨IsVonNBounded.tendsto_smallSets_nhds, _⟩ := isVonNBounded_iff_tendsto_smallSets_nhds

中文:
引理 isVonNBounded_iff_tendsto_smallSets_nhds
  结论: {𝕜 E : 类型} [NormedDivisionRing 𝕜]
  证明: by
  rw [tendsto_smallSets_iff]
  refine forall₂_congr fun V hV => ?_
  simp only [absorbs_iff_eventually_nhds_zero (mem_of_mem_nhds hV), mapsTo_iff_image_subset,
    image_smul]

alias ⟨IsVonNBounded.tendsto_smallSets_nhds, _⟩ := isVonNBounded_iff_tendsto_smallSets_nhds

Depends on / 依赖: NonUnitalNormedRing, NonUnitalNormedRing.toNormedAddCommGroup, absorbs_iff_eventually_nhds_zero, image_smul, mapsTo_iff_image_subset, mem_of_mem_nhds, tendsto_smallSets_iff, toNormedAddCommGroup
-/
lemma isVonNBounded_iff_tendsto_smallSets_nhds {𝕜 E : Type*} [NormedDivisionRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {S : Set E} :
    IsVonNBounded 𝕜 S ↔ Tendsto (· • S : 𝕜 -> Set E) (𝓝 0) (𝓝 0).smallSets := by
  rw [tendsto_smallSets_iff]
  refine forall₂_congr fun V hV => ?_
  simp only [absorbs_iff_eventually_nhds_zero (mem_of_mem_nhds hV), mapsTo_iff_image_subset,
    image_smul]

alias ⟨IsVonNBounded.tendsto_smallSets_nhds, _⟩ := isVonNBounded_iff_tendsto_smallSets_nhds

/--
lemma `isVonNBounded_iff_absorbing_le` / 引理 `isVonNBounded_iff_absorbing_le`

English:
lemma isVonNBounded_iff_absorbing_le
  statement: {𝕜 E : Type*} [NormedDivisionRing 𝕜]
  proof: .rfl

中文:
引理 isVonNBounded_iff_absorbing_le
  结论: {𝕜 E : 类型} [NormedDivisionRing 𝕜]
  证明: .rfl

Depends on / 依赖: NonUnitalSeminormedRing, NonUnitalSeminormedRing.toSeminormedAddCommGroup, toSeminormedAddCommGroup
-/
lemma isVonNBounded_iff_absorbing_le {𝕜 E : Type*} [NormedDivisionRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {S : Set E} :
    IsVonNBounded 𝕜 S ↔ Filter.absorbing 𝕜 S <= 𝓝 0 :=
  .rfl

/--
lemma `isVonNBounded_pi_iff` / 引理 `isVonNBounded_pi_iff`

English:
lemma isVonNBounded_pi_iff
  statement: {𝕜 ι : Type*} {E : ι -> Type*} [NormedDivisionRing 𝕜]
  proof: by
  simp_rw [isVonNBounded_iff_tendsto_smallSets_nhds, nhds_pi, Filter.pi, smallSets_iInf,
    smallSets_comap_eq_comap_image, tendsto_iInf, tendsto_comap_iff, Function.comp_def,
    ← image_smul, image_image, eval, Pi.smul_apply, Pi.zero_apply]

中文:
引理 isVonNBounded_pi_iff
  结论: {𝕜 ι : 类型} {E : ι -> 类型} [NormedDivisionRing 𝕜]
  证明: by
  simp_rw [isVonNBounded_iff_tendsto_smallSets_nhds, nhds_pi, Filter.pi, smallSets_iInf,
    smallSets_comap_eq_comap_image, tendsto_iInf, tendsto_comap_iff, Function.comp_def,
    ← image_smul, image_image, eval, Pi.smul_apply, Pi.zero_apply]

Depends on / 依赖: Filter, Filter.pi, Function, Function.comp_def, Pi.smul_apply, Pi.zero_apply, comp_def, image_image, image_smul, isVonNBounded_iff_tendsto_smallSets_nhds, nhds_pi, simp_rw, smallSets_comap_eq_comap_image, smallSets_iInf, smul_apply, tendsto_comap_iff, tendsto_iInf, zero_apply
-/
lemma isVonNBounded_pi_iff {𝕜 ι : Type*} {E : ι -> Type*} [NormedDivisionRing 𝕜]
    [forall i, AddCommGroup (E i)] [forall i, Module 𝕜 (E i)] [forall i, TopologicalSpace (E i)]
    {S : Set (forall i, E i)} : IsVonNBounded 𝕜 S ↔ forall i, IsVonNBounded 𝕜 (eval i '' S) := by
  simp_rw [isVonNBounded_iff_tendsto_smallSets_nhds, nhds_pi, Filter.pi, smallSets_iInf,
    smallSets_comap_eq_comap_image, tendsto_iInf, tendsto_comap_iff, Function.comp_def,
    ← image_smul, image_image, eval, Pi.smul_apply, Pi.zero_apply]

section Image

variable {𝕜₁ 𝕜₂ : Type*} [NormedDivisionRing 𝕜₁] [NormedDivisionRing 𝕜₂] [AddCommGroup E]
  [Module 𝕜₁ E] [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace E] [TopologicalSpace F]

/--
theorem `IsVonNBounded.image` / 定理 `IsVonNBounded.image`

English:
theorem IsVonNBounded.image
  statement: {σ : 𝕜₁ ->+* 𝕜₂} [RingHomSurjective σ] [RingHomIsometric σ]
  proof: by
  have : map σ (𝓝 0) = 𝓝 0 := by
    rw [σ.isometry.isEmbedding.map_nhds_eq]; rw [σ.surjective.range_eq]; rw [nhdsWithin_univ]; rw [map_zero]
  have hf₀ : Tendsto f (𝓝 0) (𝓝 0) := f.continuous.tendsto' 0 0 (map_zero f)
  simp only [isVonNBounded_iff_tendsto_smallSets_nhds, ← this, tendsto_map'_if

中文:
定理 IsVonNBounded.image
  结论: {σ : 𝕜₁ ->+* 𝕜₂} [RingHomSurjective σ] [RingHomIsometric σ]
  证明: by
  have : map σ (𝓝 0) = 𝓝 0 := by
    rw [σ.isometry.isEmbedding.map_nhds_eq]; rw [σ.surjective.range_eq]; rw [nhdsWithin_univ]; rw [map_zero]
  have hf₀ : Tendsto f (𝓝 0) (𝓝 0) := f.continuous.tendsto' 0 0 (map_zero f)
  simp only [isVonNBounded_iff_tendsto_smallSets_nhds, ← this, tendsto_map'_if
-/
protected theorem IsVonNBounded.image {σ : 𝕜₁ ->+* 𝕜₂} [RingHomSurjective σ] [RingHomIsometric σ]
    {s : Set E} (hs : IsVonNBounded 𝕜₁ s) (f : E ->SL[σ] F) : IsVonNBounded 𝕜₂ (f '' s) := by
  have : map σ (𝓝 0) = 𝓝 0 := by
    rw [σ.isometry.isEmbedding.map_nhds_eq]; rw [σ.surjective.range_eq]; rw [nhdsWithin_univ]; rw [map_zero]
  have hf₀ : Tendsto f (𝓝 0) (𝓝 0) := f.continuous.tendsto' 0 0 (map_zero f)
  simp only [isVonNBounded_iff_tendsto_smallSets_nhds, ← this, tendsto_map'_iff] at hs ⊢
  simpa only [comp_def, image_smul_setₛₗ] using hf₀.image_smallSets.comp hs

end Image

section sequence

/--
theorem `IsVonNBounded.smul_tendsto_zero` / 定理 `IsVonNBounded.smul_tendsto_zero`

English:
theorem IsVonNBounded.smul_tendsto_zero
  statement: [NormedField 𝕜]
  proof: (hS.tendsto_smallSets_nhds.comp hε).of_smallSets hxS.mono fun _ => smul_mem_smul_set

中文:
定理 IsVonNBounded.smul_tendsto_zero
  结论: [NormedField 𝕜]
  证明: (hS.tendsto_smallSets_nhds.comp hε).of_smallSets hxS.mono fun _ => smul_mem_smul_set

Depends on / 依赖: hS.tendsto_smallSets_nhds.comp, hxS.mono, of_smallSets, smul_mem_smul_set, tendsto_smallSets_nhds
-/
theorem IsVonNBounded.smul_tendsto_zero [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    {S : Set E} {ε : ι -> 𝕜} {x : ι -> E} {l : Filter ι}
    (hS : IsVonNBounded 𝕜 S) (hxS : forallᶠ n in l, x n in S) (hε : Tendsto ε l (𝓝 0)) :
    Tendsto (ε • x) l (𝓝 0) :=
(hS.tendsto_smallSets_nhds.comp hε).of_smallSets hxS.mono fun _ => smul_mem_smul_set

variable [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E]

/--
theorem `isVonNBounded_of_smul_tendsto_zero` / 定理 `isVonNBounded_of_smul_tendsto_zero`

English:
theorem isVonNBounded_of_smul_tendsto_zero
  statement: {ε : ι -> 𝕜} {l : Filter ι} [l.NeBot]
  proof: by
  rw [(nhds_basis_balanced 𝕜 E).isVonNBounded_iff]
  by_contra! ⟨V, ⟨hV, hVb⟩, hVS⟩
  have : forallᶠ n in l, exists x : S, ε n • (x : E) ∉ V := by
    filter_upwards [hε] with n hn
    rw [absorbs_iff_norm] at hVS
    push Not at hVS
    rcases hVS ‖(ε n)⁻¹‖ with ⟨a, haε, haS⟩
    rcases Set.not_

中文:
定理 isVonNBounded_of_smul_tendsto_zero
  结论: {ε : ι -> 𝕜} {l : Filter ι} [l.NeBot]
  证明: by
  rw [(nhds_basis_balanced 𝕜 E).isVonNBounded_iff]
  by_contra! ⟨V, ⟨hV, hVb⟩, hVS⟩
  have : forallᶠ n in l, exists x : S, ε n • (x : E) ∉ V := by
    filter_upwards [hε] with n hn
    rw [absorbs_iff_norm] at hVS
    push Not at hVS
    rcases hVS ‖(ε n)⁻¹‖ with ⟨a, haε, haS⟩
    rcases Set.not_

Depends on / 依赖: Eventually, Filter, Filter.Eventually.f, Filter.frequently_false, Set.mem_inv_smul_set_iff, Set.not_subset.mp, absorbs_iff_norm, choice, filter_upwards, frequently_false, hVb.smul_mono, isVonNBounded_iff, nhds_basis_balanced, not_subset, smul_mono, this.choice
-/
theorem isVonNBounded_of_smul_tendsto_zero {ε : ι -> 𝕜} {l : Filter ι} [l.NeBot]
    (hε : forallᶠ n in l, ε n != 0) {S : Set E}
    (H : forall x : ι -> E, (forall n, x n in S) -> Tendsto (ε • x) l (𝓝 0)) : IsVonNBounded 𝕜 S := by
  rw [(nhds_basis_balanced 𝕜 E).isVonNBounded_iff]
  by_contra! ⟨V, ⟨hV, hVb⟩, hVS⟩
  have : forallᶠ n in l, exists x : S, ε n • (x : E) ∉ V := by
    filter_upwards [hε] with n hn
    rw [absorbs_iff_norm] at hVS
    push Not at hVS
    rcases hVS ‖(ε n)⁻¹‖ with ⟨a, haε, haS⟩
    rcases Set.not_subset.mp haS with ⟨x, hxS, hx⟩
    refine ⟨⟨x, hxS⟩, fun hnx => ?_⟩
    rw [← Set.mem_inv_smul_set_iff₀ hn] at hnx
    exact hx (hVb.smul_mono haε hnx)
  rcases this.choice with ⟨x, hx⟩
  refine Filter.frequently_false l (Filter.Eventually.frequently ?_)
  filter_upwards [hx,
    (H (_ ∘ x) fun n => (x n).2).eventually (eventually_mem_set.mpr hV)] using fun n => id

/--
theorem `isVonNBounded_iff_smul_tendsto_zero` / 定理 `isVonNBounded_iff_smul_tendsto_zero`

English:
theorem isVonNBounded_iff_smul_tendsto_zero
  statement: {ε : ι -> 𝕜} {l : Filter ι} [l.NeBot]
  proof: ⟨fun hS _ hxS => hS.smul_tendsto_zero (Eventually.of_forall hxS) (le_trans hε nhdsWithin_le_nhds),
    isVonNBounded_of_smul_tendsto_zero (by exact hε self_mem_nhdsWithin)⟩

中文:
定理 isVonNBounded_iff_smul_tendsto_zero
  结论: {ε : ι -> 𝕜} {l : Filter ι} [l.NeBot]
  证明: ⟨fun hS _ hxS => hS.smul_tendsto_zero (Eventually.of_forall hxS) (le_trans hε nhdsWithin_le_nhds),
    isVonNBounded_of_smul_tendsto_zero (by exact hε self_mem_nhdsWithin)⟩

Depends on / 依赖: Eventually, Eventually.of_forall, hS.smul_tendsto_zero, isVonNBounded_of_smul_tendsto_zero, le_trans, nhdsWithin_le_nhds, of_forall, self_mem_nhdsWithin, smul_tendsto_zero
-/
theorem isVonNBounded_iff_smul_tendsto_zero {ε : ι -> 𝕜} {l : Filter ι} [l.NeBot]
    (hε : Tendsto ε l (𝓝[!=] 0)) {S : Set E} :
    IsVonNBounded 𝕜 S ↔ forall x : ι -> E, (forall n, x n in S) -> Tendsto (ε • x) l (𝓝 0) :=
  ⟨fun hS _ hxS => hS.smul_tendsto_zero (Eventually.of_forall hxS) (le_trans hε nhdsWithin_le_nhds),
    isVonNBounded_of_smul_tendsto_zero (by exact hε self_mem_nhdsWithin)⟩

end sequence

/--
theorem `IsVonNBounded.extend_scalars` / 定理 `IsVonNBounded.extend_scalars`

English:
theorem IsVonNBounded.extend_scalars
  statement: [NontriviallyNormedField 𝕜]
  proof: by
  obtain ⟨ε, hε, hε₀⟩ : exists ε : Nat -> 𝕜, Tendsto ε atTop (𝓝 0) ∧ forallᶠ n in atTop, ε n != 0 := by
    simpa only [tendsto_nhdsWithin_iff] using! exists_seq_tendsto (𝓝[!=] (0 : 𝕜))
  refine isVonNBounded_of_smul_tendsto_zero (ε := (ε · • 1)) (by simpa) fun x hx => ?_
  have := h.smul_tendsto

中文:
定理 IsVonNBounded.extend_scalars
  结论: [NontriviallyNormedField 𝕜]
  证明: by
  obtain ⟨ε, hε, hε₀⟩ : exists ε : Nat -> 𝕜, Tendsto ε atTop (𝓝 0) ∧ forallᶠ n in atTop, ε n != 0 := by
    simpa only [tendsto_nhdsWithin_iff] using! exists_seq_tendsto (𝓝[!=] (0 : 𝕜))
  refine isVonNBounded_of_smul_tendsto_zero (ε := (ε · • 1)) (by simpa) fun x hx => ?_
  have := h.smul_tendsto

Depends on / 依赖: Pi.smul_def, Tendsto, exists_seq_tendsto, h.smul_tendsto_zero, isVonNBounded_of_smul_tendsto_zero, of_forall, smul_def, smul_one_smul, smul_tendsto_zero, tendsto_nhdsWithin_iff
-/
theorem IsVonNBounded.extend_scalars [NontriviallyNormedField 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    (𝕝 : Type*) [NontriviallyNormedField 𝕝] [NormedAlgebra 𝕜 𝕝]
    [Module 𝕝 E] [TopologicalSpace E] [ContinuousSMul 𝕝 E] [IsScalarTower 𝕜 𝕝 E]
    {s : Set E} (h : IsVonNBounded 𝕜 s) : IsVonNBounded 𝕝 s := by
  obtain ⟨ε, hε, hε₀⟩ : exists ε : Nat -> 𝕜, Tendsto ε atTop (𝓝 0) ∧ forallᶠ n in atTop, ε n != 0 := by
    simpa only [tendsto_nhdsWithin_iff] using! exists_seq_tendsto (𝓝[!=] (0 : 𝕜))
  refine isVonNBounded_of_smul_tendsto_zero (ε := (ε · • 1)) (by simpa) fun x hx => ?_
  have := h.smul_tendsto_zero (.of_forall hx) hε
  simpa only [Pi.smul_def', smul_one_smul]

section NormedField

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E]

/--
theorem `IsVonNBounded.closure` / 定理 `IsVonNBounded.closure`

English:
theorem IsVonNBounded.closure
  statement: [T1Space E] [RegularSpace E] [ContinuousConstSMul 𝕜 E]
  proof: by
  intro V hV
  rcases exists_mem_nhds_isClosed_subset hV with ⟨W, hW₁, hW₂, hW₃⟩
  specialize ha hW₁
  filter_upwards [ha] with b ha'
  grw [ha', closure_smul₀ b, closure_subset_iff_isClosed.mpr hW₂, hW₃]

中文:
定理 IsVonNBounded.closure
  结论: [T1Space E] [RegularSpace E] [ContinuousConstSMul 𝕜 E]
  证明: by
  intro V hV
  rcases exists_mem_nhds_isClosed_subset hV with ⟨W, hW₁, hW₂, hW₃⟩
  specialize ha hW₁
  filter_upwards [ha] with b ha'
  grw [ha', closure_smul₀ b, closure_subset_iff_isClosed.mpr hW₂, hW₃]

Depends on / 依赖: closure_subset_iff_isClosed, closure_subset_iff_isClosed.mpr, exists_mem_nhds_isClosed_subset, filter_upwards, specialize
-/
theorem IsVonNBounded.closure [T1Space E] [RegularSpace E] [ContinuousConstSMul 𝕜 E]
    {a : Set E} (ha : IsVonNBounded 𝕜 a) : IsVonNBounded 𝕜 (closure a) := by
  intro V hV
  rcases exists_mem_nhds_isClosed_subset hV with ⟨W, hW₁, hW₂, hW₃⟩
  specialize ha hW₁
  filter_upwards [ha] with b ha'
  grw [ha', closure_smul₀ b, closure_subset_iff_isClosed.mpr hW₂, hW₃]

variable [ContinuousSMul 𝕜 E]

/--
theorem `isVonNBounded_singleton` / 定理 `isVonNBounded_singleton`

English:
theorem isVonNBounded_singleton
  given: (x : E)
  statement: IsVonNBounded 𝕜 ({x} : Set E)
  proof: fun _ hV =>
  (absorbent_nhds_zero hV).absorbs

@[simp]

中文:
定理 isVonNBounded_singleton
  条件: (x : E)
  结论: IsVonNBounded 𝕜 ({x} : Set E)
  证明: fun _ hV =>
  (absorbent_nhds_zero hV).absorbs

@[simp]
-/
theorem isVonNBounded_singleton (x : E) : IsVonNBounded 𝕜 ({x} : Set E) := fun _ hV =>
  (absorbent_nhds_zero hV).absorbs

@[simp]
/--
theorem `isVonNBounded_insert` / 定理 `isVonNBounded_insert`

English:
theorem isVonNBounded_insert
  given: (x : E) {s : Set E}
  proof: by
  simp only [← singleton_union, isVonNBounded_union, isVonNBounded_singleton, true_and]

protected alias ⟨_, IsVonNBounded.insert⟩ := isVonNBounded_insert

中文:
定理 isVonNBounded_insert
  条件: (x : E) {s : Set E}
  证明: by
  simp only [← singleton_union, isVonNBounded_union, isVonNBounded_singleton, true_and]

protected alias ⟨_, IsVonNBounded.insert⟩ := isVonNBounded_insert

Depends on / 依赖: isVonNBounded_singleton, isVonNBounded_union, singleton_union, true_and
-/
theorem isVonNBounded_insert (x : E) {s : Set E} :
    IsVonNBounded 𝕜 (insert x s) ↔ IsVonNBounded 𝕜 s := by
  simp only [← singleton_union, isVonNBounded_union, isVonNBounded_singleton, true_and]

protected alias ⟨_, IsVonNBounded.insert⟩ := isVonNBounded_insert

/--
theorem `_root_.Set.Finite.isVonNBounded` / 定理 `_root_.Set.Finite.isVonNBounded`

English:
theorem _root_.Set.Finite.isVonNBounded
  given: {s : Set E} (hs : s.Finite)
  proof: fun _ hV =>
  (absorbent_nhds_zero hV).absorbs_finite hs

中文:
定理 _root_.Set.Finite.isVonNBounded
  条件: {s : Set E} (hs : s.Finite)
  证明: fun _ hV =>
  (absorbent_nhds_zero hV).absorbs_finite hs
-/
theorem _root_.Set.Finite.isVonNBounded {s : Set E} (hs : s.Finite) :
    IsVonNBounded 𝕜 s := fun _ hV =>
  (absorbent_nhds_zero hV).absorbs_finite hs

section ContinuousAdd

variable [ContinuousAdd E] {s t : Set E}

/--
theorem `IsVonNBounded.vadd` / 定理 `IsVonNBounded.vadd`

English:
theorem IsVonNBounded.vadd
  given: (hs : IsVonNBounded 𝕜 s) (x : E)
  proof: by
  rw [← singleton_vadd]
  -- TODO: dot notation timeouts in the next line
  exact IsVonNBounded.add (isVonNBounded_singleton x) hs

@[simp]

中文:
定理 IsVonNBounded.vadd
  条件: (hs : IsVonNBounded 𝕜 s) (x : E)
  证明: by
  rw [← singleton_vadd]
  -- TODO: dot notation timeouts in the next line
  exact IsVonNBounded.add (isVonNBounded_singleton x) hs

@[simp]
-/
protected theorem IsVonNBounded.vadd (hs : IsVonNBounded 𝕜 s) (x : E) :
    IsVonNBounded 𝕜 (x +ᵥ s) := by
  rw [← singleton_vadd]
  -- TODO: dot notation timeouts in the next line
  exact IsVonNBounded.add (isVonNBounded_singleton x) hs

@[simp]
/--
theorem `isVonNBounded_vadd` / 定理 `isVonNBounded_vadd`

English:
theorem isVonNBounded_vadd
  given: (x : E)
  statement: IsVonNBounded 𝕜 (x +ᵥ s) ↔ IsVonNBounded 𝕜 s
  proof: ⟨fun h => by simpa using h.vadd (-x), fun h => h.vadd x⟩

中文:
定理 isVonNBounded_vadd
  条件: (x : E)
  结论: IsVonNBounded 𝕜 (x +ᵥ s) ↔ IsVonNBounded 𝕜 s
  证明: ⟨fun h => by simpa using h.vadd (-x), fun h => h.vadd x⟩

Depends on / 依赖: h.vadd
-/
theorem isVonNBounded_vadd (x : E) : IsVonNBounded 𝕜 (x +ᵥ s) ↔ IsVonNBounded 𝕜 s :=
  ⟨fun h => by simpa using h.vadd (-x), fun h => h.vadd x⟩

/--
theorem `IsVonNBounded.of_add_right` / 定理 `IsVonNBounded.of_add_right`

English:
theorem IsVonNBounded.of_add_right
  given: (hst : IsVonNBounded 𝕜 (s + t)) (hs : s.Nonempty)
  proof: let ⟨x, hx⟩ := hs
(isVonNBounded_vadd x).mp hst.subset image_subset_image2_right hx

中文:
定理 IsVonNBounded.of_add_right
  条件: (hst : IsVonNBounded 𝕜 (s + t)) (hs : s.Nonempty)
  证明: let ⟨x, hx⟩ := hs
(isVonNBounded_vadd x).mp hst.subset image_subset_image2_right hx

Depends on / 依赖: hst.subset, image_subset_image2_right, isVonNBounded_vadd, subset
-/
theorem IsVonNBounded.of_add_right (hst : IsVonNBounded 𝕜 (s + t)) (hs : s.Nonempty) :
    IsVonNBounded 𝕜 t :=
  let ⟨x, hx⟩ := hs
(isVonNBounded_vadd x).mp hst.subset image_subset_image2_right hx

/--
theorem `IsVonNBounded.of_add_left` / 定理 `IsVonNBounded.of_add_left`

English:
theorem IsVonNBounded.of_add_left
  given: (hst : IsVonNBounded 𝕜 (s + t)) (ht : t.Nonempty)
  proof: ((add_comm s t).subst hst).of_add_right ht

中文:
定理 IsVonNBounded.of_add_left
  条件: (hst : IsVonNBounded 𝕜 (s + t)) (ht : t.Nonempty)
  证明: ((add_comm s t).subst hst).of_add_right ht

Depends on / 依赖: add_comm, of_add_right
-/
theorem IsVonNBounded.of_add_left (hst : IsVonNBounded 𝕜 (s + t)) (ht : t.Nonempty) :
    IsVonNBounded 𝕜 s :=
  ((add_comm s t).subst hst).of_add_right ht

/--
theorem `isVonNBounded_add_of_nonempty` / 定理 `isVonNBounded_add_of_nonempty`

English:
theorem isVonNBounded_add_of_nonempty
  given: (hs : s.Nonempty) (ht : t.Nonempty)
  proof: ⟨fun h => ⟨h.of_add_left ht, h.of_add_right hs⟩, and_imp.2 IsVonNBounded.add⟩

中文:
定理 isVonNBounded_add_of_nonempty
  条件: (hs : s.Nonempty) (ht : t.Nonempty)
  证明: ⟨fun h => ⟨h.of_add_left ht, h.of_add_right hs⟩, and_imp.2 IsVonNBounded.add⟩

Depends on / 依赖: IsVonNBounded, IsVonNBounded.add, and_imp, h.of_add_left, h.of_add_right, of_add_left, of_add_right
-/
theorem isVonNBounded_add_of_nonempty (hs : s.Nonempty) (ht : t.Nonempty) :
    IsVonNBounded 𝕜 (s + t) ↔ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t :=
  ⟨fun h => ⟨h.of_add_left ht, h.of_add_right hs⟩, and_imp.2 IsVonNBounded.add⟩

/--
theorem `isVonNBounded_add` / 定理 `isVonNBounded_add`

English:
theorem isVonNBounded_add
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hs; · simp
  rcases t.eq_empty_or_nonempty with rfl | ht; · simp
  simp [hs.ne_empty, ht.ne_empty, isVonNBounded_add_of_nonempty hs ht]

@[simp]

中文:
定理 isVonNBounded_add
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hs; · simp
  rcases t.eq_empty_or_nonempty with rfl | ht; · simp
  simp [hs.ne_empty, ht.ne_empty, isVonNBounded_add_of_nonempty hs ht]

@[simp]

Depends on / 依赖: NonUnitalSubalgebraClass, NonUnitalSubalgebraClass.nonUnitalSeminormedRing, eq_empty_or_nonempty, hs.ne_empty, ht.ne_empty, isVonNBounded_add_of_nonempty, ne_empty, nonUnitalSeminormedRing, s.eq_empty_or_nonempty, t.eq_empty_or_nonempty
-/
theorem isVonNBounded_add :
    IsVonNBounded 𝕜 (s + t) ↔ s = ∅ ∨ t = ∅ ∨ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t := by
  rcases s.eq_empty_or_nonempty with rfl | hs; · simp
  rcases t.eq_empty_or_nonempty with rfl | ht; · simp
  simp [hs.ne_empty, ht.ne_empty, isVonNBounded_add_of_nonempty hs ht]

@[simp]
/--
theorem `isVonNBounded_add_self` / 定理 `isVonNBounded_add_self`

English:
theorem isVonNBounded_add_self
  statement: IsVonNBounded 𝕜 (s + s) ↔ IsVonNBounded 𝕜 s
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hs <;> simp [isVonNBounded_add_of_nonempty, *]

中文:
定理 isVonNBounded_add_self
  结论: IsVonNBounded 𝕜 (s + s) ↔ IsVonNBounded 𝕜 s
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hs <;> simp [isVonNBounded_add_of_nonempty, *]

Depends on / 依赖: eq_empty_or_nonempty, isVonNBounded_add_of_nonempty, s.eq_empty_or_nonempty
-/
theorem isVonNBounded_add_self : IsVonNBounded 𝕜 (s + s) ↔ IsVonNBounded 𝕜 s := by
  rcases s.eq_empty_or_nonempty with rfl | hs <;> simp [isVonNBounded_add_of_nonempty, *]

/--
theorem `IsVonNBounded.of_sub_left` / 定理 `IsVonNBounded.of_sub_left`

English:
theorem IsVonNBounded.of_sub_left
  given: (hst : IsVonNBounded 𝕜 (s - t)) (ht : t.Nonempty)
  proof: ((sub_eq_add_neg s t).subst hst).of_add_left ht.neg

中文:
定理 IsVonNBounded.of_sub_left
  条件: (hst : IsVonNBounded 𝕜 (s - t)) (ht : t.Nonempty)
  证明: ((sub_eq_add_neg s t).subst hst).of_add_left ht.neg

Depends on / 依赖: NonUnitalSubalgebraClass, NonUnitalSubalgebraClass.nonUnitalNormedRing, ht.neg, nonUnitalNormedRing, of_add_left, sub_eq_add_neg
-/
theorem IsVonNBounded.of_sub_left (hst : IsVonNBounded 𝕜 (s - t)) (ht : t.Nonempty) :
    IsVonNBounded 𝕜 s :=
  ((sub_eq_add_neg s t).subst hst).of_add_left ht.neg

end ContinuousAdd

section IsTopologicalAddGroup

variable [IsTopologicalAddGroup E] {s t : Set E}

/--
theorem `IsVonNBounded.of_sub_right` / 定理 `IsVonNBounded.of_sub_right`

English:
theorem IsVonNBounded.of_sub_right
  given: (hst : IsVonNBounded 𝕜 (s - t)) (hs : s.Nonempty)
  proof: (((sub_eq_add_neg s t).subst hst).of_add_right hs).of_neg

中文:
定理 IsVonNBounded.of_sub_right
  条件: (hst : IsVonNBounded 𝕜 (s - t)) (hs : s.Nonempty)
  证明: (((sub_eq_add_neg s t).subst hst).of_add_right hs).of_neg

Depends on / 依赖: of_add_right, of_neg, sub_eq_add_neg
-/
theorem IsVonNBounded.of_sub_right (hst : IsVonNBounded 𝕜 (s - t)) (hs : s.Nonempty) :
    IsVonNBounded 𝕜 t :=
  (((sub_eq_add_neg s t).subst hst).of_add_right hs).of_neg

/--
theorem `isVonNBounded_sub_of_nonempty` / 定理 `isVonNBounded_sub_of_nonempty`

English:
theorem isVonNBounded_sub_of_nonempty
  given: (hs : s.Nonempty) (ht : t.Nonempty)
  proof: by
  simp [sub_eq_add_neg, isVonNBounded_add_of_nonempty, hs, ht]

中文:
定理 isVonNBounded_sub_of_nonempty
  条件: (hs : s.Nonempty) (ht : t.Nonempty)
  证明: by
  simp [sub_eq_add_neg, isVonNBounded_add_of_nonempty, hs, ht]

Depends on / 依赖: isVonNBounded_add_of_nonempty, sub_eq_add_neg
-/
theorem isVonNBounded_sub_of_nonempty (hs : s.Nonempty) (ht : t.Nonempty) :
    IsVonNBounded 𝕜 (s - t) ↔ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t := by
  simp [sub_eq_add_neg, isVonNBounded_add_of_nonempty, hs, ht]

/--
theorem `isVonNBounded_sub` / 定理 `isVonNBounded_sub`

English:
theorem isVonNBounded_sub
  proof: by
  simp [sub_eq_add_neg, isVonNBounded_add]

中文:
定理 isVonNBounded_sub
  证明: by
  simp [sub_eq_add_neg, isVonNBounded_add]

Depends on / 依赖: isVonNBounded_add, sub_eq_add_neg
-/
theorem isVonNBounded_sub :
    IsVonNBounded 𝕜 (s - t) ↔ s = ∅ ∨ t = ∅ ∨ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t := by
  simp [sub_eq_add_neg, isVonNBounded_add]

end IsTopologicalAddGroup

/--
theorem `sUnion_isVonNBounded_eq_univ` / 定理 `sUnion_isVonNBounded_eq_univ`

English:
theorem sUnion_isVonNBounded_eq_univ
  statement: ⋃₀ Set.ofPred (IsVonNBounded 𝕜) = (Set.univ : Set E)
  proof: Set.eq_univ_iff_forall.mpr fun x =>
    Set.mem_sUnion.mpr ⟨{x}, isVonNBounded_singleton _, Set.mem_singleton _⟩

中文:
定理 sUnion_isVonNBounded_eq_univ
  结论: ⋃₀ Set.ofPred (IsVonNBounded 𝕜) = (Set.univ : Set E)
  证明: Set.eq_univ_iff_forall.mpr fun x =>
    Set.mem_sUnion.mpr ⟨{x}, isVonNBounded_singleton _, Set.mem_singleton _⟩

Depends on / 依赖: Set.eq_univ_iff_forall.mpr, Set.mem_sUnion.mpr, Set.mem_singleton, eq_univ_iff_forall, isVonNBounded_singleton, mem_sUnion, mem_singleton
-/
theorem sUnion_isVonNBounded_eq_univ : ⋃₀ Set.ofPred (IsVonNBounded 𝕜) = (Set.univ : Set E) :=
  Set.eq_univ_iff_forall.mpr fun x =>
    Set.mem_sUnion.mpr ⟨{x}, isVonNBounded_singleton _, Set.mem_singleton _⟩

variable (𝕜 E)

-- See note [reducible non-instances]
/--
Definition of `vonNBornology` / `vonNBornology` 的定义

English:
abbreviation vonNBornology
  signature: : Bornology E
  body: Bornology.ofBounded (Set.ofPred (IsVonNBounded 𝕜)) (isVonNBounded_empty 𝕜 E)
    (fun _ hs _ ht => hs.subset ht) (fun _ hs _ => hs.union) isVonNBounded_singleton

中文:
缩写 vonNBornology
  签名: : Bornology E
  定义体: Bornology.ofBounded (Set.ofPred (IsVonNBounded 𝕜)) (isVonNBounded_empty 𝕜 E)
    (fun _ hs _ ht => hs.subset ht) (fun _ hs _ => hs.union) isVonNBounded_singleton

Depends on / 依赖: Bornology, Bornology.ofBounded, CommRing, IsVonNBounded, Set.ofPred, SubalgebraClass, SubalgebraClass.seminormedRing, hs.subset, hs.union, isVonNBounded_empty, isVonNBounded_singleton, ofBounded, ofPred, seminormedRing, subset
-/
abbrev vonNBornology : Bornology E :=
  Bornology.ofBounded (Set.ofPred (IsVonNBounded 𝕜)) (isVonNBounded_empty 𝕜 E)
    (fun _ hs _ ht => hs.subset ht) (fun _ hs _ => hs.union) isVonNBounded_singleton

variable {E}

@[simp]
/--
theorem `isBounded_iff_isVonNBounded` / 定理 `isBounded_iff_isVonNBounded`

English:
theorem isBounded_iff_isVonNBounded
  given: {s : Set E}
  proof: isBounded_ofBounded_iff _

中文:
定理 isBounded_iff_isVonNBounded
  条件: {s : Set E}
  证明: isBounded_ofBounded_iff _

Depends on / 依赖: isBounded_ofBounded_iff
-/
theorem isBounded_iff_isVonNBounded {s : Set E} :
    @IsBounded _ (vonNBornology 𝕜 E) s ↔ IsVonNBounded 𝕜 s :=
  isBounded_ofBounded_iff _

end NormedField

end Bornology

section IsUniformAddGroup

variable (𝕜) [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]

/--
theorem `TotallyBounded.isVonNBounded` / 定理 `TotallyBounded.isVonNBounded`

English:
theorem TotallyBounded.isVonNBounded
  given: {s : Set E} (hs : TotallyBounded s)
  proof: by
  if h : exists x : 𝕜, 1 < ‖x‖ then
    let : NontriviallyNormedField 𝕜 := ⟨h⟩
    rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero] at hs
    intro U hU
    have h : Filter.Tendsto (fun x : E × E => x.fst + x.snd) (𝓝 0) (𝓝 0) :=
      continuous_add.tendsto' _ _ (zero_add _)
    have h' := 

中文:
定理 TotallyBounded.isVonNBounded
  条件: {s : Set E} (hs : TotallyBounded s)
  证明: by
  if h : exists x : 𝕜, 1 < ‖x‖ then
    let : NontriviallyNormedField 𝕜 := ⟨h⟩
    rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero] at hs
    intro U hU
    have h : Filter.Tendsto (fun x : E × E => x.fst + x.snd) (𝓝 0) (𝓝 0) :=
      continuous_add.tendsto' _ _ (zero_add _)
    have h' := 

Depends on / 依赖: Absorbs, Absorbs.mono_right, CommRing, Filter, Filter.Tendsto, NontriviallyNormedField, SubalgebraClass, SubalgebraClass.normedRing, Tendsto, absorbs_biU, basis_left, continuous_add, continuous_add.tendsto, h.basis_left, ht.absorbs_biU, mono_right, nhds_basis_balanced, nhds_prod_eq, normedRing, simp_rw
-/
theorem TotallyBounded.isVonNBounded {s : Set E} (hs : TotallyBounded s) :
    Bornology.IsVonNBounded 𝕜 s := by
  if h : exists x : 𝕜, 1 < ‖x‖ then
    let : NontriviallyNormedField 𝕜 := ⟨h⟩
    rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero] at hs
    intro U hU
    have h : Filter.Tendsto (fun x : E × E => x.fst + x.snd) (𝓝 0) (𝓝 0) :=
      continuous_add.tendsto' _ _ (zero_add _)
    have h' := (nhds_basis_balanced 𝕜 E).prod (nhds_basis_balanced 𝕜 E)
    simp_rw [← nhds_prod_eq, id] at h'
    rcases h.basis_left h' U hU with ⟨x, hx, h''⟩
    rcases hs x.snd hx.2.1 with ⟨t, ht, hs⟩
    refine Absorbs.mono_right ?_ hs
    rw [ht.absorbs_biUnion]
    have hx_fstsnd : x.fst + x.snd subseteq U := add_subset_iff.mpr fun z1 hz1 z2 hz2 =>
h'' mk_mem_prod hz1 hz2
    refine fun y _ => Absorbs.mono_left ?_ hx_fstsnd
    exact (absorbent_nhds_zero hx.1.1).vadd_absorbs hx.2.2.absorbs_self
  else
    have : BoundedSpace 𝕜 := ⟨Metric.isBounded_iff.2 ⟨1, by simp_all [dist_eq_norm]⟩⟩
    exact Bornology.IsVonNBounded.of_boundedSpace

end IsUniformAddGroup

variable (𝕜) in
/--
theorem `IsCompact.isVonNBounded` / 定理 `IsCompact.isVonNBounded`

English:
theorem IsCompact.isVonNBounded
  statement: [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  proof: letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI := isUniformAddGroup_of_addCommGroup (G := E)
  hs.totallyBounded.isVonNBounded 𝕜

中文:
定理 IsCompact.isVonNBounded
  结论: [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  证明: letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI := isUniformAddGroup_of_addCommGroup (G := E)
  hs.totallyBounded.isVonNBounded 𝕜

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, hs.totallyBounded.isVonNBounded, isUniformAddGroup_of_addCommGroup, isVonNBounded, rightUniformSpace, totallyBounded
-/
theorem IsCompact.isVonNBounded [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] {s : Set E}
    (hs : IsCompact s) : Bornology.IsVonNBounded 𝕜 s :=
  letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI := isUniformAddGroup_of_addCommGroup (G := E)
  hs.totallyBounded.isVonNBounded 𝕜

variable (𝕜) in
/--
theorem `Filter.Tendsto.isVonNBounded_range` / 定理 `Filter.Tendsto.isVonNBounded_range`

English:
theorem Filter.Tendsto.isVonNBounded_range
  statement: [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  proof: letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI := isUniformAddGroup_of_addCommGroup (G := E)
  hf.cauchySeq.totallyBounded_range.isVonNBounded 𝕜

中文:
定理 Filter.Tendsto.isVonNBounded_range
  结论: [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  证明: letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI := isUniformAddGroup_of_addCommGroup (G := E)
  hf.cauchySeq.totallyBounded_range.isVonNBounded 𝕜

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, cauchySeq, hf.cauchySeq.totallyBounded_range.isVonNBounded, isUniformAddGroup_of_addCommGroup, isVonNBounded, rightUniformSpace, totallyBounded_range
-/
theorem Filter.Tendsto.isVonNBounded_range [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    {f : Nat -> E} {x : E} (hf : Tendsto f atTop (𝓝 x)) : Bornology.IsVonNBounded 𝕜 (range f) :=
  letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI := isUniformAddGroup_of_addCommGroup (G := E)
  hf.cauchySeq.totallyBounded_range.isVonNBounded 𝕜

variable (𝕜) in
/--
theorem `Bornology.IsVonNBounded.restrict_scalars_of_nontrivial` / 定理 `Bornology.IsVonNBounded.restrict_scalars_of_nontrivial`

English:
theorem Bornology.IsVonNBounded.restrict_scalars_of_nontrivial
  proof: by
  intro V hV
refine (h hV).restrict_scalars AntilipschitzWith.tendsto_cobounded (K := ‖(1 : 𝕜')‖₊⁻¹) ?_
  refine AntilipschitzWith.of_le_mul_nndist fun x y => ?_
  rw [nndist_eq_nnnorm]; rw [nndist_eq_nnnorm]; rw [← sub_smul]; rw [nnnorm_smul]; rw [← div_eq_inv_mul]; rw [mul_div_cancel_right₀ _ (

中文:
定理 Bornology.IsVonNBounded.restrict_scalars_of_nontrivial
  证明: by
  intro V hV
refine (h hV).restrict_scalars AntilipschitzWith.tendsto_cobounded (K := ‖(1 : 𝕜')‖₊⁻¹) ?_
  refine AntilipschitzWith.of_le_mul_nndist fun x y => ?_
  rw [nndist_eq_nnnorm]; rw [nndist_eq_nnnorm]; rw [← sub_smul]; rw [nnnorm_smul]; rw [← div_eq_inv_mul]; rw [mul_div_cancel_right₀ _ (
-/
protected theorem Bornology.IsVonNBounded.restrict_scalars_of_nontrivial
    [NormedField 𝕜] [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Nontrivial 𝕜']
    [Zero E] [TopologicalSpace E]
    [SMul 𝕜 E] [MulAction 𝕜' E] [IsScalarTower 𝕜 𝕜' E] {s : Set E}
    (h : IsVonNBounded 𝕜' s) : IsVonNBounded 𝕜 s := by
  intro V hV
refine (h hV).restrict_scalars AntilipschitzWith.tendsto_cobounded (K := ‖(1 : 𝕜')‖₊⁻¹) ?_
  refine AntilipschitzWith.of_le_mul_nndist fun x y => ?_
  rw [nndist_eq_nnnorm]; rw [nndist_eq_nnnorm]; rw [← sub_smul]; rw [nnnorm_smul]; rw [← div_eq_inv_mul]; rw [mul_div_cancel_right₀ _ (nnnorm_ne_zero_iff.2 one_ne_zero)]

variable (𝕜) in
/--
theorem `Bornology.IsVonNBounded.restrict_scalars` / 定理 `Bornology.IsVonNBounded.restrict_scalars`

English:
theorem Bornology.IsVonNBounded.restrict_scalars
  proof: match subsingleton_or_nontrivial 𝕜' with
  | .inl _ =>
    have : Subsingleton E := MulActionWithZero.subsingleton 𝕜' E
    IsVonNBounded.of_subsingleton
  | .inr _ =>
    h.restrict_scalars_of_nontrivial _

中文:
定理 Bornology.IsVonNBounded.restrict_scalars
  证明: match subsingleton_or_nontrivial 𝕜' with
  | .inl _ =>
    have : Subsingleton E := MulActionWithZero.subsingleton 𝕜' E
    IsVonNBounded.of_subsingleton
  | .inr _ =>
    h.restrict_scalars_of_nontrivial _
-/
protected theorem Bornology.IsVonNBounded.restrict_scalars
    [NormedField 𝕜] [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [Zero E] [TopologicalSpace E]
    [SMul 𝕜 E] [MulActionWithZero 𝕜' E] [IsScalarTower 𝕜 𝕜' E] {s : Set E}
    (h : IsVonNBounded 𝕜' s) : IsVonNBounded 𝕜 s :=
  match subsingleton_or_nontrivial 𝕜' with
  | .inl _ =>
    have : Subsingleton E := MulActionWithZero.subsingleton 𝕜' E
    IsVonNBounded.of_subsingleton
  | .inr _ =>
    h.restrict_scalars_of_nontrivial _

section VonNBornologyEqMetric

namespace NormedSpace

section NormedField

variable (𝕜)
variable [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
theorem `isVonNBounded_of_isBounded` / 定理 `isVonNBounded_of_isBounded`

English:
theorem isVonNBounded_of_isBounded
  given: {s : Set E} (h : Bornology.IsBounded s)
  proof: by
  rcases h.subset_ball 0 with ⟨r, hr⟩
  rw [Metric.nhds_basis_ball.isVonNBounded_iff]
  rw [← ball_normSeminorm 𝕜 E] at hr ⊢
  exact fun ε hε => ((normSeminorm 𝕜 E).ball_zero_absorbs_ball_zero hε).mono_right hr

中文:
定理 isVonNBounded_of_isBounded
  条件: {s : Set E} (h : Bornology.IsBounded s)
  证明: by
  rcases h.subset_ball 0 with ⟨r, hr⟩
  rw [Metric.nhds_basis_ball.isVonNBounded_iff]
  rw [← ball_normSeminorm 𝕜 E] at hr ⊢
  exact fun ε hε => ((normSeminorm 𝕜 E).ball_zero_absorbs_ball_zero hε).mono_right hr

Depends on / 依赖: Metric, Metric.nhds_basis_ball.isVonNBounded_iff, ball_normSeminorm, ball_zero_absorbs_ball_zero, h.subset_ball, isVonNBounded_iff, mono_right, nhds_basis_ball, normSeminorm, subset_ball
-/
theorem isVonNBounded_of_isBounded {s : Set E} (h : Bornology.IsBounded s) :
    Bornology.IsVonNBounded 𝕜 s := by
  rcases h.subset_ball 0 with ⟨r, hr⟩
  rw [Metric.nhds_basis_ball.isVonNBounded_iff]
  rw [← ball_normSeminorm 𝕜 E] at hr ⊢
  exact fun ε hε => ((normSeminorm 𝕜 E).ball_zero_absorbs_ball_zero hε).mono_right hr

variable (E)

/--
theorem `isVonNBounded_ball` / 定理 `isVonNBounded_ball`

English:
theorem isVonNBounded_ball
  given: (r : Real)
  statement: Bornology.IsVonNBounded 𝕜 (Metric.ball (0 : E) r)
  proof: isVonNBounded_of_isBounded _ Metric.isBounded_ball

中文:
定理 isVonNBounded_ball
  条件: (r : 实数)
  结论: Bornology.IsVonNBounded 𝕜 (Metric.ball (0 : E) r)
  证明: isVonNBounded_of_isBounded _ Metric.isBounded_ball

Depends on / 依赖: Metric, Metric.isBounded_ball, isBounded_ball, isVonNBounded_of_isBounded
-/
theorem isVonNBounded_ball (r : Real) : Bornology.IsVonNBounded 𝕜 (Metric.ball (0 : E) r) :=
  isVonNBounded_of_isBounded _ Metric.isBounded_ball

/--
theorem `isVonNBounded_closedBall` / 定理 `isVonNBounded_closedBall`

English:
theorem isVonNBounded_closedBall
  given: (r : Real)
  proof: isVonNBounded_of_isBounded _ Metric.isBounded_closedBall

中文:
定理 isVonNBounded_closedBall
  条件: (r : 实数)
  证明: isVonNBounded_of_isBounded _ Metric.isBounded_closedBall

Depends on / 依赖: Metric, Metric.isBounded_closedBall, isBounded_closedBall, isVonNBounded_of_isBounded
-/
theorem isVonNBounded_closedBall (r : Real) :
    Bornology.IsVonNBounded 𝕜 (Metric.closedBall (0 : E) r) :=
  isVonNBounded_of_isBounded _ Metric.isBounded_closedBall

end NormedField

variable (𝕜)
variable [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
theorem `isVonNBounded_iff` / 定理 `isVonNBounded_iff`

English:
theorem isVonNBounded_iff
  given: {s : Set E}
  statement: Bornology.IsVonNBounded 𝕜 s ↔ Bornology.IsBounded s
  proof: by
  refine ⟨fun h => ?_, isVonNBounded_of_isBounded _⟩
  rcases (h (Metric.ball_mem_nhds 0 zero_lt_one)).exists_pos with ⟨ρ, hρ, hρball⟩
  rcases NormedField.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩
  specialize hρball a ha.le
  rw [← ball_normSeminorm 𝕜 E]; rw [Seminorm.smul_ball_zero (norm_pos_iff.1 <| hρ

中文:
定理 isVonNBounded_iff
  条件: {s : Set E}
  结论: Bornology.IsVonNBounded 𝕜 s ↔ Bornology.IsBounded s
  证明: by
  refine ⟨fun h => ?_, isVonNBounded_of_isBounded _⟩
  rcases (h (Metric.ball_mem_nhds 0 zero_lt_one)).exists_pos with ⟨ρ, hρ, hρball⟩
  rcases NormedField.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩
  specialize hρball a ha.le
  rw [← ball_normSeminorm 𝕜 E]; rw [Seminorm.smul_ball_zero (norm_pos_iff.1 <| hρ

Depends on / 依赖: Metric, Metric.ball_mem_nhds, Metric.isBounded_ball.subset, NormedField, NormedField.exists_lt_norm, Seminorm, Seminorm.smul_ball_zero, ball_mem_nhds, ball_normSeminorm, exists_lt_norm, exists_pos, ha.le, isBounded_ball, isVonNBounded_of_isBounded, norm_pos_iff, smul_ball_zero, specialize, subset, zero_lt_one
-/
theorem isVonNBounded_iff {s : Set E} : Bornology.IsVonNBounded 𝕜 s ↔ Bornology.IsBounded s := by
  refine ⟨fun h => ?_, isVonNBounded_of_isBounded _⟩
  rcases (h (Metric.ball_mem_nhds 0 zero_lt_one)).exists_pos with ⟨ρ, hρ, hρball⟩
  rcases NormedField.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩
  specialize hρball a ha.le
  rw [← ball_normSeminorm 𝕜 E]; rw [Seminorm.smul_ball_zero (norm_pos_iff.1 <| hρ.trans ha)]; rw [ball_normSeminorm] at hρball
  exact Metric.isBounded_ball.subset hρball

/--
theorem `isVonNBounded_iff'` / 定理 `isVonNBounded_iff'`

English:
theorem isVonNBounded_iff'
  given: {s : Set E}
  proof: by
  rw [NormedSpace.isVonNBounded_iff]; rw [isBounded_iff_forall_norm_le]

中文:
定理 isVonNBounded_iff'
  条件: {s : Set E}
  证明: by
  rw [NormedSpace.isVonNBounded_iff]; rw [isBounded_iff_forall_norm_le]

Depends on / 依赖: NormedSpace, NormedSpace.isVonNBounded_iff, isBounded_iff_forall_norm_le, isVonNBounded_iff
-/
theorem isVonNBounded_iff' {s : Set E} :
    Bornology.IsVonNBounded 𝕜 s ↔ exists r : Real, forall x in s, ‖x‖ <= r := by
  rw [NormedSpace.isVonNBounded_iff]; rw [isBounded_iff_forall_norm_le]

/--
theorem `image_isVonNBounded_iff` / 定理 `image_isVonNBounded_iff`

English:
theorem image_isVonNBounded_iff
  given: {α : Type*} {f : α -> E} {s : Set α}
  proof: by
  simp_rw [isVonNBounded_iff', Set.forall_mem_image]

中文:
定理 image_isVonNBounded_iff
  条件: {α : 类型} {f : α -> E} {s : Set α}
  证明: by
  simp_rw [isVonNBounded_iff', Set.forall_mem_image]

Depends on / 依赖: Set.forall_mem_image, forall_mem_image, isVonNBounded_iff, simp_rw
-/
theorem image_isVonNBounded_iff {α : Type*} {f : α -> E} {s : Set α} :
    Bornology.IsVonNBounded 𝕜 (f '' s) ↔ exists r : Real, forall x in s, ‖f x‖ <= r := by
  simp_rw [isVonNBounded_iff', Set.forall_mem_image]

/--
theorem `vonNBornology_eq` / 定理 `vonNBornology_eq`

English:
theorem vonNBornology_eq
  statement: Bornology.vonNBornology 𝕜 E = PseudoMetricSpace.toBornology
  proof: by
  rw [Bornology.ext_iff_isBounded]
  intro s
  rw [Bornology.isBounded_iff_isVonNBounded]
  exact isVonNBounded_iff _

中文:
定理 vonNBornology_eq
  结论: Bornology.vonNBornology 𝕜 E = PseudoMetricSpace.toBornology
  证明: by
  rw [Bornology.ext_iff_isBounded]
  intro s
  rw [Bornology.isBounded_iff_isVonNBounded]
  exact isVonNBounded_iff _

Depends on / 依赖: Bornology, Bornology.ext_iff_isBounded, Bornology.isBounded_iff_isVonNBounded, ext_iff_isBounded, isBounded_iff_isVonNBounded, isVonNBounded_iff
-/
theorem vonNBornology_eq : Bornology.vonNBornology 𝕜 E = PseudoMetricSpace.toBornology := by
  rw [Bornology.ext_iff_isBounded]
  intro s
  rw [Bornology.isBounded_iff_isVonNBounded]
  exact isVonNBounded_iff _

/--
theorem `isBounded_iff_subset_smul_ball` / 定理 `isBounded_iff_subset_smul_ball`

English:
theorem isBounded_iff_subset_smul_ball
  given: {s : Set E}
  proof: by
  rw [← isVonNBounded_iff 𝕜]
  constructor
  · intro h
    rcases (h (Metric.ball_mem_nhds 0 zero_lt_one)).exists_pos with ⟨ρ, _, hρball⟩
    rcases NormedField.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩
    exact ⟨a, hρball a ha.le⟩
  · rintro ⟨a, ha⟩
    exact ((isVonNBounded_ball 𝕜 E 1).image (a • (1 : E

中文:
定理 isBounded_iff_subset_smul_ball
  条件: {s : Set E}
  证明: by
  rw [← isVonNBounded_iff 𝕜]
  constructor
  · intro h
    rcases (h (Metric.ball_mem_nhds 0 zero_lt_one)).exists_pos with ⟨ρ, _, hρball⟩
    rcases NormedField.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩
    exact ⟨a, hρball a ha.le⟩
  · rintro ⟨a, ha⟩
    exact ((isVonNBounded_ball 𝕜 E 1).image (a • (1 : E

Depends on / 依赖: Metric, Metric.ball_mem_nhds, NormedField, NormedField.exists_lt_norm, ball_mem_nhds, exists_lt_norm, exists_pos, ha.le, isVonNBounded_ball, isVonNBounded_iff, subset, zero_lt_one
-/
theorem isBounded_iff_subset_smul_ball {s : Set E} :
    Bornology.IsBounded s ↔ exists a : 𝕜, s subseteq a • Metric.ball (0 : E) 1 := by
  rw [← isVonNBounded_iff 𝕜]
  constructor
  · intro h
    rcases (h (Metric.ball_mem_nhds 0 zero_lt_one)).exists_pos with ⟨ρ, _, hρball⟩
    rcases NormedField.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩
    exact ⟨a, hρball a ha.le⟩
  · rintro ⟨a, ha⟩
    exact ((isVonNBounded_ball 𝕜 E 1).image (a • (1 : E ->L[𝕜] E))).subset ha

/--
theorem `isBounded_iff_subset_smul_closedBall` / 定理 `isBounded_iff_subset_smul_closedBall`

English:
theorem isBounded_iff_subset_smul_closedBall
  given: {s : Set E}
  proof: by
  constructor
  · rw [isBounded_iff_subset_smul_ball 𝕜]
exact Exists.imp fun a ha => ha.trans Set.smul_set_mono Metric.ball_subset_closedBall
  · rw [← isVonNBounded_iff 𝕜]
    rintro ⟨a, ha⟩
    exact ((isVonNBounded_closedBall 𝕜 E 1).image (a • (1 : E ->L[𝕜] E))).subset ha

中文:
定理 isBounded_iff_subset_smul_closedBall
  条件: {s : Set E}
  证明: by
  constructor
  · rw [isBounded_iff_subset_smul_ball 𝕜]
exact Exists.imp fun a ha => ha.trans Set.smul_set_mono Metric.ball_subset_closedBall
  · rw [← isVonNBounded_iff 𝕜]
    rintro ⟨a, ha⟩
    exact ((isVonNBounded_closedBall 𝕜 E 1).image (a • (1 : E ->L[𝕜] E))).subset ha

Depends on / 依赖: Exists, Exists.imp, Metric, Metric.ball_subset_closedBall, Set.smul_set_mono, ball_subset_closedBall, ha.trans, isBounded_iff_subset_smul_ball, isVonNBounded_closedBall, isVonNBounded_iff, smul_set_mono, subset
-/
theorem isBounded_iff_subset_smul_closedBall {s : Set E} :
    Bornology.IsBounded s ↔ exists a : 𝕜, s subseteq a • Metric.closedBall (0 : E) 1 := by
  constructor
  · rw [isBounded_iff_subset_smul_ball 𝕜]
exact Exists.imp fun a ha => ha.trans Set.smul_set_mono Metric.ball_subset_closedBall
  · rw [← isVonNBounded_iff 𝕜]
    rintro ⟨a, ha⟩
    exact ((isVonNBounded_closedBall 𝕜 E 1).image (a • (1 : E ->L[𝕜] E))).subset ha

end NormedSpace

end VonNBornologyEqMetric

section QuasiCompleteSpace

/--
Definition of `QuasiCompleteSpace` / `QuasiCompleteSpace` 的定义

English:
class QuasiCompleteSpace
  parameters: (𝕜 : Type*) (E : Type*) [Zero E] [UniformSpace E] [SeminormedRing 𝕜]
  axioms and operations (1):
    - quasiComplete : forall ⦃s : Set E⦄, Bornology.IsVonNBounded 𝕜 s -> IsClosed s -> IsComplete s

中文:
类 QuasiCompleteSpace
  参数: (𝕜 : 类型) (E : 类型) [Zero E] [UniformSpace E] [SeminormedRing 𝕜]
  公理与运算 (1 个):
    - quasiComplete : 对任意 ⦃s : Set E⦄, Bornology.IsVonNBounded 𝕜 s -> IsClosed s -> IsComplete s
-/
class QuasiCompleteSpace (𝕜 : Type*) (E : Type*) [Zero E] [UniformSpace E] [SeminormedRing 𝕜]
    [SMul 𝕜 E] : Prop where
  /-- A locally convex space is quasi-complete if every closed and von Neumann bounded set is
  complete. -/
  quasiComplete : forall ⦃s : Set E⦄, Bornology.IsVonNBounded 𝕜 s -> IsClosed s -> IsComplete s

variable {𝕜 : Type*} {E : Type*} [Zero E] [UniformSpace E] [SeminormedRing 𝕜] [SMul 𝕜 E]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CompleteSpace
  signature: E] : QuasiCompleteSpace 𝕜 E where
  body: IsClosed.isComplete

中文:
实例 [CompleteSpace
  签名: E] : QuasiCompleteSpace 𝕜 E where
  定义体: IsClosed.isComplete

Depends on / 依赖: IsClosed, IsClosed.isComplete, isComplete
-/
instance [CompleteSpace E] : QuasiCompleteSpace 𝕜 E where
  quasiComplete _ _ := IsClosed.isComplete

/--
theorem `isCompact_closure_of_totallyBounded_quasiComplete` / 定理 `isCompact_closure_of_totallyBounded_quasiComplete`

English:
theorem isCompact_closure_of_totallyBounded_quasiComplete
  statement: {E : Type*} {𝕜 : Type*} [NormedField 𝕜]
  proof: hs.closure.isCompact_of_isComplete
    (QuasiCompleteSpace.quasiComplete (TotallyBounded.isVonNBounded 𝕜 (TotallyBounded.closure hs))
    isClosed_closure)

中文:
定理 isCompact_closure_of_totallyBounded_quasiComplete
  结论: {E : 类型} {𝕜 : 类型} [NormedField 𝕜]
  证明: hs.closure.isCompact_of_isComplete
    (QuasiCompleteSpace.quasiComplete (TotallyBounded.isVonNBounded 𝕜 (TotallyBounded.closure hs))
    isClosed_closure)

Depends on / 依赖: QuasiCompleteSpace, QuasiCompleteSpace.quasiComplete, TotallyBounded, TotallyBounded.closure, TotallyBounded.isVonNBounded, closure, hs.closure.isCompact_of_isComplete, isClosed_closure, isCompact_of_isComplete, isVonNBounded, quasiComplete
-/
theorem isCompact_closure_of_totallyBounded_quasiComplete {E : Type*} {𝕜 : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [QuasiCompleteSpace 𝕜 E] {s : Set E} (hs : TotallyBounded s) : IsCompact (closure s) :=
  hs.closure.isCompact_of_isComplete
    (QuasiCompleteSpace.quasiComplete (TotallyBounded.isVonNBounded 𝕜 (TotallyBounded.closure hs))
    isClosed_closure)

end QuasiCompleteSpace
