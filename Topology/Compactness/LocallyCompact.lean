/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.Compactness.Compact
/-!
# Locally compact spaces

This file contains basic results about locally compact spaces.
-/

public section

open Set Filter Topology TopologicalSpace

variable {X : Type*} {Y : Type*} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WeaklyLocallyCompactSpace
  signature: X] [WeaklyLocallyCompactSpace Y] :
  body: let ⟨s₁, hc₁, h₁⟩ := exists_compact_mem_nhds x.1
    let ⟨s₂, hc₂, h₂⟩ := exists_compact_mem_nhds x.2
    ⟨s₁ ×ˢ s₂, hc₁.prod hc₂, prod_mem_nhds h₁ h₂⟩

中文:
实例 [WeaklyLocallyCompact空间
  签名: X] [WeaklyLocallyCompact空间 Y] :
  定义体: let ⟨s₁, hc₁, h₁⟩ := exists_compact_mem_nhds x.1
    let ⟨s₂, hc₂, h₂⟩ := exists_compact_mem_nhds x.2
    ⟨s₁ ×ˢ s₂, hc₁.prod hc₂, prod_mem_nhds h₁ h₂⟩

Depends on / 依赖: exists_compact_mem_nhds, prod_mem_nhds
-/
instance [WeaklyLocallyCompactSpace X] [WeaklyLocallyCompactSpace Y] :
    WeaklyLocallyCompactSpace (X × Y) where
  exists_compact_mem_nhds x :=
    let ⟨s₁, hc₁, h₁⟩ := exists_compact_mem_nhds x.1
    let ⟨s₂, hc₂, h₂⟩ := exists_compact_mem_nhds x.2
    ⟨s₁ ×ˢ s₂, hc₁.prod hc₂, prod_mem_nhds h₁ h₂⟩

instance {ι : Type*} [Finite ι] {X : ι -> Type*} [(i : ι) -> TopologicalSpace (X i)]
    [(i : ι) -> WeaklyLocallyCompactSpace (X i)] :
    WeaklyLocallyCompactSpace ((i : ι) -> X i) where
  exists_compact_mem_nhds f := by
    choose s hsc hs using fun i => exists_compact_mem_nhds (f i)
    exact ⟨pi univ s, isCompact_univ_pi hsc, set_pi_mem_nhds univ.toFinite fun i _ => hs i⟩

instance (priority := 100) [CompactSpace X] : WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds _ := ⟨univ, isCompact_univ, univ_mem⟩

/--
theorem `Topology.IsClosedEmbedding.weaklyLocallyCompactSpace` / 定理 `Topology.IsClosedEmbedding.weaklyLocallyCompactSpace`

English:
theorem Topology.IsClosedEmbedding.weaklyLocallyCompactSpace
  statement: [WeaklyLocallyCompactSpace Y]
  proof: let ⟨K, hK, hKx⟩ := exists_compact_mem_nhds (f x)
    ⟨f ⁻¹' K, hf.isCompact_preimage hK, hf.continuous.continuousAt hKx⟩

中文:
定理 拓扑.是闭嵌入.weaklyLocallyCompactSpace
  结论: [WeaklyLocallyCompact空间 Y]
  证明: let ⟨K, hK, hKx⟩ := exists_compact_mem_nhds (f x)
    ⟨f ⁻¹' K, hf.isCompact_preimage hK, hf.continuous.continuousAt hKx⟩
-/
protected theorem Topology.IsClosedEmbedding.weaklyLocallyCompactSpace [WeaklyLocallyCompactSpace Y]
    {f : X -> Y} (hf : IsClosedEmbedding f) : WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds x :=
    let ⟨K, hK, hKx⟩ := exists_compact_mem_nhds (f x)
    ⟨f ⁻¹' K, hf.isCompact_preimage hK, hf.continuous.continuousAt hKx⟩

/--
theorem `IsClosed.weaklyLocallyCompactSpace` / 定理 `IsClosed.weaklyLocallyCompactSpace`

English:
theorem IsClosed.weaklyLocallyCompactSpace
  statement: [WeaklyLocallyCompactSpace X]
  proof: hs.isClosedEmbedding_subtypeVal.weaklyLocallyCompactSpace

中文:
定理 是闭集.weaklyLocallyCompactSpace
  结论: [WeaklyLocallyCompact空间 X]
  证明: hs.isClosedEmbedding_subtypeVal.weaklyLocallyCompactSpace
-/
protected theorem IsClosed.weaklyLocallyCompactSpace [WeaklyLocallyCompactSpace X]
    {s : Set X} (hs : IsClosed s) : WeaklyLocallyCompactSpace s :=
  hs.isClosedEmbedding_subtypeVal.weaklyLocallyCompactSpace

/--
theorem `IsOpenQuotientMap.weaklyLocallyCompactSpace` / 定理 `IsOpenQuotientMap.weaklyLocallyCompactSpace`

English:
theorem IsOpenQuotientMap.weaklyLocallyCompactSpace
  statement: [WeaklyLocallyCompactSpace X]
  proof: by
    refine hf.surjective.forall.2 fun x => ?_
    rcases exists_compact_mem_nhds x with ⟨K, hKc, hKx⟩
    exact ⟨f '' K, hKc.image hf.continuous, hf.isOpenMap.image_mem_nhds hKx⟩

中文:
定理 是OpenQuotient映射.weaklyLocallyCompactSpace
  结论: [WeaklyLocallyCompact空间 X]
  证明: by
    refine hf.surjective.forall.2 fun x => ?_
    rcases exists_compact_mem_nhds x with ⟨K, hKc, hKx⟩
    exact ⟨f '' K, hKc.image hf.continuous, hf.isOpenMap.image_mem_nhds hKx⟩

Depends on / 依赖: continuous, exists_compact_mem_nhds, hKc.image, hf.continuous, hf.isOpenMap.image_mem_nhds, hf.surjective.forall, image_mem_nhds, isOpenMap, surjective
-/
theorem IsOpenQuotientMap.weaklyLocallyCompactSpace [WeaklyLocallyCompactSpace X]
    {f : X -> Y} (hf : IsOpenQuotientMap f) : WeaklyLocallyCompactSpace Y where
  exists_compact_mem_nhds := by
    refine hf.surjective.forall.2 fun x => ?_
    rcases exists_compact_mem_nhds x with ⟨K, hKc, hKx⟩
    exact ⟨f '' K, hKc.image hf.continuous, hf.isOpenMap.image_mem_nhds hKx⟩

/--
theorem `exists_compact_superset` / 定理 `exists_compact_superset`

English:
theorem exists_compact_superset
  given: [WeaklyLocallyCompactSpace X] {K : Set X} (hK : IsCompact K)
  proof: by
  choose s hc hmem using fun x : X => exists_compact_mem_nhds x
  rcases hK.elim_nhds_subcover _ fun x _ => interior_mem_nhds.2 (hmem x) with ⟨I, -, hIK⟩
  refine ⟨⋃ x in I, s x, I.isCompact_biUnion fun _ _ => hc _, hIK.trans ?_⟩
exact iUnion₂_subset fun x hx => interior_mono subset_iUnion₂ (s := fun x _ => s x) x hx

中文:
定理 存在_compact_superset
  条件: [WeaklyLocallyCompact空间 X] {K : 集合 X} (hK : 是紧集 K)
  证明: by
  choose s hc hmem using fun x : X => exists_compact_mem_nhds x
  rcases hK.elim_nhds_subcover _ fun x _ => interior_mem_nhds.2 (hmem x) with ⟨I, -, hIK⟩
  refine ⟨⋃ x in I, s x, I.isCompact_biUnion fun _ _ => hc _, hIK.trans ?_⟩
exact iUnion₂_subset fun x hx => interior_mono subset_iUnion₂ (s := fun x _ => s x) x hx

Depends on / 依赖: I.isCompact_biUnion, elim_nhds_subcover, exists_compact_mem_nhds, hIK.trans, hK.elim_nhds_subcover, interior_mem_nhds, interior_mono, isCompact_biUnion
-/
theorem exists_compact_superset [WeaklyLocallyCompactSpace X] {K : Set X} (hK : IsCompact K) :
    exists K', IsCompact K' ∧ K subseteq interior K' := by
  choose s hc hmem using fun x : X => exists_compact_mem_nhds x
  rcases hK.elim_nhds_subcover _ fun x _ => interior_mem_nhds.2 (hmem x) with ⟨I, -, hIK⟩
  refine ⟨⋃ x in I, s x, I.isCompact_biUnion fun _ _ => hc _, hIK.trans ?_⟩
exact iUnion₂_subset fun x hx => interior_mono subset_iUnion₂ (s := fun x _ => s x) x hx

/--
theorem `disjoint_nhds_cocompact` / 定理 `disjoint_nhds_cocompact`

English:
theorem disjoint_nhds_cocompact
  given: [WeaklyLocallyCompactSpace X] (x : X)
  proof: let ⟨_, hc, hx⟩ := exists_compact_mem_nhds x
  disjoint_of_disjoint_of_mem disjoint_compl_right hx hc.compl_mem_cocompact

中文:
定理 disjoint_nhds_cocompact
  条件: [WeaklyLocallyCompact空间 X] (x : X)
  证明: let ⟨_, hc, hx⟩ := exists_compact_mem_nhds x
  disjoint_of_disjoint_of_mem disjoint_compl_right hx hc.compl_mem_cocompact

Depends on / 依赖: compl_mem_cocompact, disjoint_compl_right, disjoint_of_disjoint_of_mem, exists_compact_mem_nhds, hc.compl_mem_cocompact
-/
theorem disjoint_nhds_cocompact [WeaklyLocallyCompactSpace X] (x : X) :
    Disjoint (𝓝 x) (cocompact X) :=
  let ⟨_, hc, hx⟩ := exists_compact_mem_nhds x
  disjoint_of_disjoint_of_mem disjoint_compl_right hx hc.compl_mem_cocompact

/--
theorem `compact_basis_nhds` / 定理 `compact_basis_nhds`

English:
theorem compact_basis_nhds
  given: [LocallyCompactSpace X] (x : X)
  proof: hasBasis_self.2 by simpa only [and_comm] using LocallyCompactSpace.local_compact_nhds x

中文:
定理 compact_basis_nhds
  条件: [局部紧空间 X] (x : X)
  证明: hasBasis_self.2 by simpa only [and_comm] using LocallyCompactSpace.local_compact_nhds x

Depends on / 依赖: LocallyCompactSpace, LocallyCompactSpace.local_compact_nhds, and_comm, hasBasis_self, local_compact_nhds
-/
theorem compact_basis_nhds [LocallyCompactSpace X] (x : X) :
    (𝓝 x).HasBasis (fun s => s in 𝓝 x ∧ IsCompact s) fun s => s :=
hasBasis_self.2 by simpa only [and_comm] using LocallyCompactSpace.local_compact_nhds x

/--
theorem `local_compact_nhds` / 定理 `local_compact_nhds`

English:
theorem local_compact_nhds
  given: [LocallyCompactSpace X] {x : X} {n : Set X} (h : n in 𝓝 x)
  proof: LocallyCompactSpace.local_compact_nhds _ _ h

中文:
定理 local_compact_nhds
  条件: [局部紧空间 X] {x : X} {n : 集合 X} (h : n in 𝓝 x)
  证明: LocallyCompactSpace.local_compact_nhds _ _ h

Depends on / 依赖: LocallyCompactSpace, LocallyCompactSpace.local_compact_nhds, local_compact_nhds
-/
theorem local_compact_nhds [LocallyCompactSpace X] {x : X} {n : Set X} (h : n in 𝓝 x) :
    exists s in 𝓝 x, s subseteq n ∧ IsCompact s :=
  LocallyCompactSpace.local_compact_nhds _ _ h

/--
theorem `LocallyCompactSpace.of_hasBasis` / 定理 `LocallyCompactSpace.of_hasBasis`

English:
theorem LocallyCompactSpace.of_hasBasis
  statement: {ι : X -> Type*} {p : forall x, ι x -> Prop}
  proof: ⟨fun x _t ht =>
    let ⟨i, hp, ht⟩ := (h x).mem_iff.1 ht
    ⟨s x i, (h x).mem_of_mem hp, ht, hc x i hp⟩⟩

中文:
定理 局部紧空间.of_hasBasis
  结论: {ι : X -> 类型} {p : 对任意 x, ι x -> 命题}
  证明: ⟨fun x _t ht =>
    let ⟨i, hp, ht⟩ := (h x).mem_iff.1 ht
    ⟨s x i, (h x).mem_of_mem hp, ht, hc x i hp⟩⟩

Depends on / 依赖: mem_iff, mem_of_mem
-/
theorem LocallyCompactSpace.of_hasBasis {ι : X -> Type*} {p : forall x, ι x -> Prop}
    {s : forall x, ι x -> Set X} (h : forall x, (𝓝 x).HasBasis (p x) (s x))
    (hc : forall x i, p x i -> IsCompact (s x i)) : LocallyCompactSpace X :=
  ⟨fun x _t ht =>
    let ⟨i, hp, ht⟩ := (h x).mem_iff.1 ht
    ⟨s x i, (h x).mem_of_mem hp, ht, hc x i hp⟩⟩

/--
Instance `Prod.locallyCompactSpace` / 实例 `Prod.locallyCompactSpace`

English:
instance Prod.locallyCompactSpace
  signature: (X : Type*) (Y : Type*) [TopologicalSpace X]
  body: have := fun x : X × Y => (compact_basis_nhds x.1).prod_nhds' (compact_basis_nhds x.2)
  .of_hasBasis this fun _ _ ⟨⟨_, h₁⟩, _, h₂⟩ => h₁.prod h₂

中文:
实例 积类型.locallyCompactSpace
  签名: (X : 类型) (Y : 类型) [拓扑空间 X]
  定义体: have := fun x : X × Y => (compact_basis_nhds x.1).prod_nhds' (compact_basis_nhds x.2)
  .of_hasBasis this fun _ _ ⟨⟨_, h₁⟩, _, h₂⟩ => h₁.prod h₂

Depends on / 依赖: compact_basis_nhds, of_hasBasis, prod_nhds
-/
instance Prod.locallyCompactSpace (X : Type*) (Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] [LocallyCompactSpace X] [LocallyCompactSpace Y] :
    LocallyCompactSpace (X × Y) :=
  have := fun x : X × Y => (compact_basis_nhds x.1).prod_nhds' (compact_basis_nhds x.2)
  .of_hasBasis this fun _ _ ⟨⟨_, h₁⟩, _, h₂⟩ => h₁.prod h₂

section Pi

variable {X : ι -> Type*} [forall i, TopologicalSpace (X i)] [forall i, LocallyCompactSpace (X i)]

/--
Instance `Pi.locallyCompactSpace_of_finite` / 实例 `Pi.locallyCompactSpace_of_finite`

English:
instance Pi.locallyCompactSpace_of_finite
  signature: [Finite ι]
  body: ⟨fun t n hn => by
    rw [nhds_pi]; rw [Filter.mem_pi] at hn
    obtain ⟨s, -, n', hn', hsub⟩ := hn
    choose n'' hn'' hsub' hc using fun i =>
      LocallyCompactSpace.local_compact_nhds (t i) (n' i) (hn' i)
    refine ⟨(Set.univ : Set ι).pi n'', ?_, subset_trans (fun _ h => ?_) hsub, isCompact_univ_pi hc⟩
    · exact (set_pi_mem_nhds_iff (@Set.finite_univ ι _) _).mpr fun i _ => hn'' i
    · exact fun i _ => hsub' i (h i trivial)⟩

中文:
实例 依赖函数类型.locallyCompactSpace_of_finite
  签名: [有限 ι]
  定义体: ⟨fun t n hn => by
    rw [nhds_pi]; rw [Filter.mem_pi] at hn
    obtain ⟨s, -, n', hn', hsub⟩ := hn
    choose n'' hn'' hsub' hc using fun i =>
      LocallyCompactSpace.local_compact_nhds (t i) (n' i) (hn' i)
    refine ⟨(Set.univ : Set ι).pi n'', ?_, subset_trans (fun _ h => ?_) hsub, isCompact_univ_pi hc⟩
    · exact (set_pi_mem_nhds_iff (@Set.finite_univ ι _) _).mpr fun i _ => hn'' i
    · exact fun i _ => hsub' i (h i trivial)⟩

Depends on / 依赖: Filter, Filter.mem_pi, LocallyCompactSpace, LocallyCompactSpace.local_compact_nhds, Set.finite_univ, Set.univ, finite_univ, isCompact_univ_pi, local_compact_nhds, mem_pi, nhds_pi, set_pi_mem_nhds_iff, subset_trans
-/
instance Pi.locallyCompactSpace_of_finite [Finite ι] : LocallyCompactSpace (forall i, X i) :=
  ⟨fun t n hn => by
    rw [nhds_pi]; rw [Filter.mem_pi] at hn
    obtain ⟨s, -, n', hn', hsub⟩ := hn
    choose n'' hn'' hsub' hc using fun i =>
      LocallyCompactSpace.local_compact_nhds (t i) (n' i) (hn' i)
    refine ⟨(Set.univ : Set ι).pi n'', ?_, subset_trans (fun _ h => ?_) hsub, isCompact_univ_pi hc⟩
    · exact (set_pi_mem_nhds_iff (@Set.finite_univ ι _) _).mpr fun i _ => hn'' i
    · exact fun i _ => hsub' i (h i trivial)⟩

/--
Instance `Pi.locallyCompactSpace` / 实例 `Pi.locallyCompactSpace`

English:
instance Pi.locallyCompactSpace
  signature: [forall i, CompactSpace (X i)]
  body: ⟨fun t n hn => by
    rw [nhds_pi]; rw [Filter.mem_pi] at hn
    obtain ⟨s, hs, n', hn', hsub⟩ := hn
    choose n'' hn'' hsub' hc using fun i =>
      LocallyCompactSpace.local_compact_nhds (t i) (n' i) (hn' i)
    refine ⟨s.pi n'', ?_, subset_trans (fun _ => ?_) hsub, ?_⟩
    · exact (set_pi_mem_nhds_iff hs _).mpr fun i _ => hn'' i
    · exact forall₂_imp fun i _ hi' => hsub' i hi'
    · classical
      rw [← Set.univ_pi_ite]
      refine isCompact_univ_pi fun i => ?_
      by_cases h : i in s
      · rw [if_pos h]
        exact hc i
      · rw [if_neg h]
        exact CompactSpace.isCompact_univ⟩

中文:
实例 依赖函数类型.locallyCompactSpace
  签名: [对任意 i, 紧空间 (X i)]
  定义体: ⟨fun t n hn => by
    rw [nhds_pi]; rw [Filter.mem_pi] at hn
    obtain ⟨s, hs, n', hn', hsub⟩ := hn
    choose n'' hn'' hsub' hc using fun i =>
      LocallyCompactSpace.local_compact_nhds (t i) (n' i) (hn' i)
    refine ⟨s.pi n'', ?_, subset_trans (fun _ => ?_) hsub, ?_⟩
    · exact (set_pi_mem_nhds_iff hs _).mpr fun i _ => hn'' i
    · exact forall₂_imp fun i _ hi' => hsub' i hi'
    · classical
      rw [← Set.univ_pi_ite]
      refine isCompact_univ_pi fun i => ?_
      by_cases h : i in s
      · rw [if_pos h]
        exact hc i
      · rw [if_neg h]
        exact CompactSpace.isCompact_univ⟩

Depends on / 依赖: Filter, Filter.mem_pi, LocallyCompactSpace, LocallyCompactSpace.local_compact_nhds, Set.univ_pi_ite, classical, if_neg, if_pos, isCompact_univ_pi, local_compact_nhds, mem_pi, nhds_pi, s.pi, set_pi_mem_nhds_iff, subset_trans, univ_pi_ite
-/
instance Pi.locallyCompactSpace [forall i, CompactSpace (X i)] : LocallyCompactSpace (forall i, X i) :=
  ⟨fun t n hn => by
    rw [nhds_pi]; rw [Filter.mem_pi] at hn
    obtain ⟨s, hs, n', hn', hsub⟩ := hn
    choose n'' hn'' hsub' hc using fun i =>
      LocallyCompactSpace.local_compact_nhds (t i) (n' i) (hn' i)
    refine ⟨s.pi n'', ?_, subset_trans (fun _ => ?_) hsub, ?_⟩
    · exact (set_pi_mem_nhds_iff hs _).mpr fun i _ => hn'' i
    · exact forall₂_imp fun i _ hi' => hsub' i hi'
    · classical
      rw [← Set.univ_pi_ite]
      refine isCompact_univ_pi fun i => ?_
      by_cases h : i in s
      · rw [if_pos h]
        exact hc i
      · rw [if_neg h]
        exact CompactSpace.isCompact_univ⟩

/--
Instance `Function.locallyCompactSpace_of_finite` / 实例 `Function.locallyCompactSpace_of_finite`

English:
instance Function.locallyCompactSpace_of_finite
  signature: [Finite ι] [LocallyCompactSpace Y]
  body: Pi.locallyCompactSpace_of_finite

中文:
实例 函数.locallyCompactSpace_of_finite
  签名: [有限 ι] [局部紧空间 Y]
  定义体: Pi.locallyCompactSpace_of_finite

Depends on / 依赖: Pi.locallyCompactSpace_of_finite, locallyCompactSpace_of_finite
-/
instance Function.locallyCompactSpace_of_finite [Finite ι] [LocallyCompactSpace Y] :
    LocallyCompactSpace (ι -> Y) :=
  Pi.locallyCompactSpace_of_finite

/--
Instance `Function.locallyCompactSpace` / 实例 `Function.locallyCompactSpace`

English:
instance Function.locallyCompactSpace
  signature: [LocallyCompactSpace Y] [CompactSpace Y]
  body: Pi.locallyCompactSpace

中文:
实例 函数.locallyCompactSpace
  签名: [局部紧空间 Y] [紧空间 Y]
  定义体: Pi.locallyCompactSpace

Depends on / 依赖: Pi.locallyCompactSpace, locallyCompactSpace
-/
instance Function.locallyCompactSpace [LocallyCompactSpace Y] [CompactSpace Y] :
    LocallyCompactSpace (ι -> Y) :=
  Pi.locallyCompactSpace

end Pi

instance (priority := 900) [LocallyCompactSpace X] : LocallyCompactPair X Y where
  exists_mem_nhds_isCompact_mapsTo hf hs :=
    let ⟨K, hKx, hKs, hKc⟩ := local_compact_nhds (hf.continuousAt hs); ⟨K, hKx, hKc, hKs⟩

instance (priority := 100) [LocallyCompactSpace X] : WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds (x : X) :=
    let ⟨K, hx, _, hKc⟩ := local_compact_nhds (x := x) univ_mem; ⟨K, hKc, hx⟩

/--
theorem `exists_compact_subset` / 定理 `exists_compact_subset`

English:
theorem exists_compact_subset
  statement: [LocallyCompactSpace X] {x : X} {U : Set X} (hU : IsOpen U)
  proof: by
  rcases LocallyCompactSpace.local_compact_nhds x U (hU.mem_nhds hx) with ⟨K, h1K, h2K, h3K⟩
  exact ⟨K, h3K, mem_interior_iff_mem_nhds.2 h1K, h2K⟩

中文:
定理 存在_compact_subset
  结论: [局部紧空间 X] {x : X} {U : 集合 X} (hU : 是开集 U)
  证明: by
  rcases LocallyCompactSpace.local_compact_nhds x U (hU.mem_nhds hx) with ⟨K, h1K, h2K, h3K⟩
  exact ⟨K, h3K, mem_interior_iff_mem_nhds.2 h1K, h2K⟩

Depends on / 依赖: LocallyCompactSpace, LocallyCompactSpace.local_compact_nhds, hU.mem_nhds, local_compact_nhds, mem_interior_iff_mem_nhds, mem_nhds
-/
theorem exists_compact_subset [LocallyCompactSpace X] {x : X} {U : Set X} (hU : IsOpen U)
    (hx : x in U) : exists K : Set X, IsCompact K ∧ x in interior K ∧ K subseteq U := by
  rcases LocallyCompactSpace.local_compact_nhds x U (hU.mem_nhds hx) with ⟨K, h1K, h2K, h3K⟩
  exact ⟨K, h3K, mem_interior_iff_mem_nhds.2 h1K, h2K⟩

/--
lemma `exists_mem_nhdsSet_isCompact_mapsTo` / 引理 `exists_mem_nhdsSet_isCompact_mapsTo`

English:
lemma exists_mem_nhdsSet_isCompact_mapsTo
  statement: [LocallyCompactPair X Y] {f : X -> Y} {K : Set X}
  proof: by
  choose! V hxV hVc hVU using fun x (hx : x in K) =>
    exists_mem_nhds_isCompact_mapsTo hf (hU.mem_nhds (hKU hx))
  rcases hK.elim_nhds_subcover_nhdsSet hxV with ⟨s, hsK, hKs⟩
  exact ⟨_, hKs, s.isCompact_biUnion fun x hx => hVc x (hsK x hx), mapsTo_iUnion₂.2 fun x hx =>
    hVU x (hsK x hx)⟩

中文:
引理 存在_mem_nhdsSet_isCompact_mapsTo
  结论: [LocallyCompactPair X Y] {f : X -> Y} {K : 集合 X}
  证明: by
  choose! V hxV hVc hVU using fun x (hx : x in K) =>
    exists_mem_nhds_isCompact_mapsTo hf (hU.mem_nhds (hKU hx))
  rcases hK.elim_nhds_subcover_nhdsSet hxV with ⟨s, hsK, hKs⟩
  exact ⟨_, hKs, s.isCompact_biUnion fun x hx => hVc x (hsK x hx), mapsTo_iUnion₂.2 fun x hx =>
    hVU x (hsK x hx)⟩

Depends on / 依赖: elim_nhds_subcover_nhdsSet, exists_mem_nhds_isCompact_mapsTo, hK.elim_nhds_subcover_nhdsSet, hU.mem_nhds, isCompact_biUnion, mem_nhds, s.isCompact_biUnion
-/
lemma exists_mem_nhdsSet_isCompact_mapsTo [LocallyCompactPair X Y] {f : X -> Y} {K : Set X}
    {U : Set Y} (hf : Continuous f) (hK : IsCompact K) (hU : IsOpen U) (hKU : MapsTo f K U) :
    exists L in 𝓝ˢ K, IsCompact L ∧ MapsTo f L U := by
  choose! V hxV hVc hVU using fun x (hx : x in K) =>
    exists_mem_nhds_isCompact_mapsTo hf (hU.mem_nhds (hKU hx))
  rcases hK.elim_nhds_subcover_nhdsSet hxV with ⟨s, hsK, hKs⟩
  exact ⟨_, hKs, s.isCompact_biUnion fun x hx => hVc x (hsK x hx), mapsTo_iUnion₂.2 fun x hx =>
    hVU x (hsK x hx)⟩

/--
theorem `exists_compact_between` / 定理 `exists_compact_between`

English:
theorem exists_compact_between
  statement: [LocallyCompactSpace X] {K U : Set X} (hK : IsCompact K)
  proof: let ⟨L, hKL, hL, hLU⟩ := exists_mem_nhdsSet_isCompact_mapsTo continuous_id hK hU h_KU
  ⟨L, hL, subset_interior_iff_mem_nhdsSet.2 hKL, hLU⟩

中文:
定理 存在_compact_between
  结论: [局部紧空间 X] {K U : 集合 X} (hK : 是紧集 K)
  证明: let ⟨L, hKL, hL, hLU⟩ := exists_mem_nhdsSet_isCompact_mapsTo continuous_id hK hU h_KU
  ⟨L, hL, subset_interior_iff_mem_nhdsSet.2 hKL, hLU⟩

Depends on / 依赖: continuous_id, exists_mem_nhdsSet_isCompact_mapsTo, h_KU, subset_interior_iff_mem_nhdsSet
-/
theorem exists_compact_between [LocallyCompactSpace X] {K U : Set X} (hK : IsCompact K)
    (hU : IsOpen U) (h_KU : K subseteq U) : exists L, IsCompact L ∧ K subseteq interior L ∧ L subseteq U :=
  let ⟨L, hKL, hL, hLU⟩ := exists_mem_nhdsSet_isCompact_mapsTo continuous_id hK hU h_KU
  ⟨L, hL, subset_interior_iff_mem_nhdsSet.2 hKL, hLU⟩

/--
theorem `IsCompact.nhdsSet_basis_isCompact` / 定理 `IsCompact.nhdsSet_basis_isCompact`

English:
theorem IsCompact.nhdsSet_basis_isCompact
  given: [LocallyCompactSpace X] {K : Set X} (hK : IsCompact K)
  proof: by
  rw [hasBasis_self]; rw [(hasBasis_nhdsSet _).forall_iff (by grind)]
  intro U ⟨hU, h_KU⟩
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU h_KU
  exact ⟨L, by rwa [← subset_interior_iff_mem_nhdsSet], hL, hLU⟩

中文:
定理 是紧集.nhdsSet_basis_isCompact
  条件: [局部紧空间 X] {K : 集合 X} (hK : 是紧集 K)
  证明: by
  rw [hasBasis_self]; rw [(hasBasis_nhdsSet _).forall_iff (by grind)]
  intro U ⟨hU, h_KU⟩
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU h_KU
  exact ⟨L, by rwa [← subset_interior_iff_mem_nhdsSet], hL, hLU⟩

Depends on / 依赖: exists_compact_between, forall_iff, h_KU, hasBasis_nhdsSet, hasBasis_self, subset_interior_iff_mem_nhdsSet
-/
theorem IsCompact.nhdsSet_basis_isCompact [LocallyCompactSpace X] {K : Set X} (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis (fun L => L in 𝓝ˢ K ∧ IsCompact L) id := by
  rw [hasBasis_self]; rw [(hasBasis_nhdsSet _).forall_iff (by grind)]
  intro U ⟨hU, h_KU⟩
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU h_KU
  exact ⟨L, by rwa [← subset_interior_iff_mem_nhdsSet], hL, hLU⟩

/--
theorem `IsOpenQuotientMap.locallyCompactSpace` / 定理 `IsOpenQuotientMap.locallyCompactSpace`

English:
theorem IsOpenQuotientMap.locallyCompactSpace
  statement: [LocallyCompactSpace X] {f : X -> Y}
  proof: by
    refine hf.surjective.forall.2 fun x U hU => ?_
    rcases local_compact_nhds (hf.continuous.continuousAt hU) with ⟨K, hKx, hKU, hKc⟩
    exact ⟨f '' K, hf.isOpenMap.image_mem_nhds hKx, image_subset_iff.2 hKU, hKc.image hf.continuous⟩

中文:
定理 是OpenQuotient映射.locallyCompactSpace
  结论: [局部紧空间 X] {f : X -> Y}
  证明: by
    refine hf.surjective.forall.2 fun x U hU => ?_
    rcases local_compact_nhds (hf.continuous.continuousAt hU) with ⟨K, hKx, hKU, hKc⟩
    exact ⟨f '' K, hf.isOpenMap.image_mem_nhds hKx, image_subset_iff.2 hKU, hKc.image hf.continuous⟩

Depends on / 依赖: continuous, continuousAt, hKc.image, hf.continuous, hf.continuous.continuousAt, hf.isOpenMap.image_mem_nhds, hf.surjective.forall, image_mem_nhds, image_subset_iff, isOpenMap, local_compact_nhds, surjective
-/
theorem IsOpenQuotientMap.locallyCompactSpace [LocallyCompactSpace X] {f : X -> Y}
    (hf : IsOpenQuotientMap f) : LocallyCompactSpace Y where
  local_compact_nhds := by
    refine hf.surjective.forall.2 fun x U hU => ?_
    rcases local_compact_nhds (hf.continuous.continuousAt hU) with ⟨K, hKx, hKU, hKc⟩
    exact ⟨f '' K, hf.isOpenMap.image_mem_nhds hKx, image_subset_iff.2 hKU, hKc.image hf.continuous⟩

/--
theorem `Topology.IsInducing.locallyCompactSpace` / 定理 `Topology.IsInducing.locallyCompactSpace`

English:
theorem Topology.IsInducing.locallyCompactSpace
  statement: [LocallyCompactSpace Y] {f : X -> Y}
  proof: by
  rcases h with ⟨U, Z, hU, hZ, hUZ⟩
  have (x : X) : (𝓝 x).HasBasis (fun s => (s in 𝓝 (f x) ∧ IsCompact s) ∧ s subseteq U)
      (fun s => f ⁻¹' (s inter Z)) := by
    have H : U in 𝓝 (f x) := hU.mem_nhds (hUZ.subset <| mem_range_self _).1
    rw [hf.nhds_eq_comap]; rw [← comap_nhdsWithin_range]; rw [hUZ]; rw [nhdsWithin_inter_of_mem (nhdsWithin_le_nhds H)]
    exact (nhdsWithin_hasBasis ((compact_basis_nhds (f x)).restrict_subset H) _).comap _
  refine .of_hasBasis this fun x s ⟨⟨_, hs⟩, hsU⟩ => ?_
  rw [hf.isCompact_preimage_iff]
  exacts [hs.inter_right hZ, hUZ ▸ by gcongr]

中文:
定理 拓扑.是Inducing.locallyCompactSpace
  结论: [局部紧空间 Y] {f : X -> Y}
  证明: by
  rcases h with ⟨U, Z, hU, hZ, hUZ⟩
  have (x : X) : (𝓝 x).HasBasis (fun s => (s in 𝓝 (f x) ∧ IsCompact s) ∧ s subseteq U)
      (fun s => f ⁻¹' (s inter Z)) := by
    have H : U in 𝓝 (f x) := hU.mem_nhds (hUZ.subset <| mem_range_self _).1
    rw [hf.nhds_eq_comap]; rw [← comap_nhdsWithin_range]; rw [hUZ]; rw [nhdsWithin_inter_of_mem (nhdsWithin_le_nhds H)]
    exact (nhdsWithin_hasBasis ((compact_basis_nhds (f x)).restrict_subset H) _).comap _
  refine .of_hasBasis this fun x s ⟨⟨_, hs⟩, hsU⟩ => ?_
  rw [hf.isCompact_preimage_iff]
  exacts [hs.inter_right hZ, hUZ ▸ by gcongr]

Depends on / 依赖: HasBasis, IsCompact, comap_nhdsWithin_range, compact_basis_nhds, hU.mem_nhds, hUZ.subset, hf.isCompact, hf.nhds_eq_comap, isCompact, mem_nhds, mem_range_self, nhdsWithin_hasBasis, nhdsWithin_inter_of_mem, nhdsWithin_le_nhds, nhds_eq_comap, of_hasBasis, restrict_subset, subset, subseteq
-/
theorem Topology.IsInducing.locallyCompactSpace [LocallyCompactSpace Y] {f : X -> Y}
    (hf : IsInducing f) (h : IsLocallyClosed (range f)) : LocallyCompactSpace X := by
  rcases h with ⟨U, Z, hU, hZ, hUZ⟩
  have (x : X) : (𝓝 x).HasBasis (fun s => (s in 𝓝 (f x) ∧ IsCompact s) ∧ s subseteq U)
      (fun s => f ⁻¹' (s inter Z)) := by
    have H : U in 𝓝 (f x) := hU.mem_nhds (hUZ.subset <| mem_range_self _).1
    rw [hf.nhds_eq_comap]; rw [← comap_nhdsWithin_range]; rw [hUZ]; rw [nhdsWithin_inter_of_mem (nhdsWithin_le_nhds H)]
    exact (nhdsWithin_hasBasis ((compact_basis_nhds (f x)).restrict_subset H) _).comap _
  refine .of_hasBasis this fun x s ⟨⟨_, hs⟩, hsU⟩ => ?_
  rw [hf.isCompact_preimage_iff]
  exacts [hs.inter_right hZ, hUZ ▸ by gcongr]

/--
theorem `Topology.IsClosedEmbedding.locallyCompactSpace` / 定理 `Topology.IsClosedEmbedding.locallyCompactSpace`

English:
theorem Topology.IsClosedEmbedding.locallyCompactSpace
  statement: [LocallyCompactSpace Y] {f : X -> Y}
  proof: hf.isInducing.locallyCompactSpace hf.isClosed_range.isLocallyClosed

中文:
定理 拓扑.是闭嵌入.locallyCompactSpace
  结论: [局部紧空间 Y] {f : X -> Y}
  证明: hf.isInducing.locallyCompactSpace hf.isClosed_range.isLocallyClosed
-/
protected theorem Topology.IsClosedEmbedding.locallyCompactSpace [LocallyCompactSpace Y] {f : X -> Y}
    (hf : IsClosedEmbedding f) : LocallyCompactSpace X :=
  hf.isInducing.locallyCompactSpace hf.isClosed_range.isLocallyClosed

/--
theorem `Topology.IsOpenEmbedding.locallyCompactSpace` / 定理 `Topology.IsOpenEmbedding.locallyCompactSpace`

English:
theorem Topology.IsOpenEmbedding.locallyCompactSpace
  statement: [LocallyCompactSpace Y] {f : X -> Y}
  proof: hf.isInducing.locallyCompactSpace hf.isOpen_range.isLocallyClosed

中文:
定理 拓扑.是开嵌入.locallyCompactSpace
  结论: [局部紧空间 Y] {f : X -> Y}
  证明: hf.isInducing.locallyCompactSpace hf.isOpen_range.isLocallyClosed
-/
protected theorem Topology.IsOpenEmbedding.locallyCompactSpace [LocallyCompactSpace Y] {f : X -> Y}
    (hf : IsOpenEmbedding f) : LocallyCompactSpace X :=
  hf.isInducing.locallyCompactSpace hf.isOpen_range.isLocallyClosed

/--
theorem `IsLocallyClosed.locallyCompactSpace` / 定理 `IsLocallyClosed.locallyCompactSpace`

English:
theorem IsLocallyClosed.locallyCompactSpace
  statement: [LocallyCompactSpace X] {s : Set X}
  proof: IsEmbedding.subtypeVal.locallyCompactSpace by rwa [Subtype.range_val]

中文:
定理 IsLocallyClosed.locallyCompactSpace
  结论: [局部紧空间 X] {s : 集合 X}
  证明: IsEmbedding.subtypeVal.locallyCompactSpace by rwa [Subtype.range_val]
-/
protected theorem IsLocallyClosed.locallyCompactSpace [LocallyCompactSpace X] {s : Set X}
    (hs : IsLocallyClosed s) : LocallyCompactSpace s :=
IsEmbedding.subtypeVal.locallyCompactSpace by rwa [Subtype.range_val]

/--
theorem `IsClosed.locallyCompactSpace` / 定理 `IsClosed.locallyCompactSpace`

English:
theorem IsClosed.locallyCompactSpace
  statement: [LocallyCompactSpace X] {s : Set X}
  proof: hs.isLocallyClosed.locallyCompactSpace

中文:
定理 是闭集.locallyCompactSpace
  结论: [局部紧空间 X] {s : 集合 X}
  证明: hs.isLocallyClosed.locallyCompactSpace
-/
protected theorem IsClosed.locallyCompactSpace [LocallyCompactSpace X] {s : Set X}
    (hs : IsClosed s) : LocallyCompactSpace s :=
  hs.isLocallyClosed.locallyCompactSpace

/--
theorem `IsOpen.locallyCompactSpace` / 定理 `IsOpen.locallyCompactSpace`

English:
theorem IsOpen.locallyCompactSpace
  given: [LocallyCompactSpace X] {s : Set X} (hs : IsOpen s)
  proof: hs.isLocallyClosed.locallyCompactSpace

中文:
定理 是开集.locallyCompactSpace
  条件: [局部紧空间 X] {s : 集合 X} (hs : 是开集 s)
  证明: hs.isLocallyClosed.locallyCompactSpace
-/
protected theorem IsOpen.locallyCompactSpace [LocallyCompactSpace X] {s : Set X} (hs : IsOpen s) :
    LocallyCompactSpace s :=
  hs.isLocallyClosed.locallyCompactSpace
