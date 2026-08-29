/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Sigma-compactness in topological spaces

## Main definitions
* `IsSigmaCompact`: a set that is the union of countably many compact sets.
* `SigmaCompactSpace X`: `X` is a σ-compact topological space; i.e., is the union
  of a countable collection of compact subspaces.

-/

@[expose] public section

open Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

/--
Definition of `IsSigmaCompact` / `IsSigmaCompact` 的定义

English:
definition IsSigmaCompact
  signature: (s : Set X)
  body: exists K : Nat -> Set X, (forall n, IsCompact (K n)) ∧ ⋃ n, K n = s

中文:
定义 IsSigmaCompact
  签名: (s : 集合 X)
  定义体: exists K : Nat -> Set X, (forall n, IsCompact (K n)) ∧ ⋃ n, K n = s

Depends on / 依赖: IsCompact
-/
def IsSigmaCompact (s : Set X) : Prop :=
  exists K : Nat -> Set X, (forall n, IsCompact (K n)) ∧ ⋃ n, K n = s

/--
lemma `IsCompact.isSigmaCompact` / 引理 `IsCompact.isSigmaCompact`

English:
lemma IsCompact.isSigmaCompact
  given: {s : Set X} (hs : IsCompact s)
  statement: IsSigmaCompact s
  proof: ⟨fun _ => s, fun _ => hs, iUnion_const _⟩

中文:
引理 是紧集.isSigmaCompact
  条件: {s : 集合 X} (hs : 是紧集 s)
  结论: IsSigmaCompact s
  证明: ⟨fun _ => s, fun _ => hs, iUnion_const _⟩

Depends on / 依赖: iUnion_const
-/
lemma IsCompact.isSigmaCompact {s : Set X} (hs : IsCompact s) : IsSigmaCompact s :=
  ⟨fun _ => s, fun _ => hs, iUnion_const _⟩

/-- The empty set is σ-compact. -/
@[simp]
/--
lemma `isSigmaCompact_empty` / 引理 `isSigmaCompact_empty`

English:
lemma isSigmaCompact_empty
  statement: IsSigmaCompact (∅ : Set X)
  proof: IsCompact.isSigmaCompact isCompact_empty

中文:
引理 isSigmaCompact_empty
  结论: IsSigmaCompact (∅ : 集合 X)
  证明: IsCompact.isSigmaCompact isCompact_empty

Depends on / 依赖: IsCompact, IsCompact.isSigmaCompact, isCompact_empty, isSigmaCompact
-/
lemma isSigmaCompact_empty : IsSigmaCompact (∅ : Set X) :=
  IsCompact.isSigmaCompact isCompact_empty

/--
lemma `isSigmaCompact_iUnion_of_isCompact` / 引理 `isSigmaCompact_iUnion_of_isCompact`

English:
lemma isSigmaCompact_iUnion_of_isCompact
  statement: [hι : Countable ι] (s : ι -> Set X)
  proof: by
  rcases isEmpty_or_nonempty ι
  · simp only [iUnion_of_empty, isSigmaCompact_empty]
  · -- If ι is non-empty, choose a surjection f : ℕ → ι, this yields a map ℕ → Set X.
    obtain ⟨f, hf⟩ := countable_iff_exists_surjective.mp hι
    exact ⟨s ∘ f, fun n => hcomp (f n), Function.Surjective.iUnion

中文:
引理 isSigmaCompact_iUnion_of_isCompact
  结论: [hι : 可数 ι] (s : ι -> 集合 X)
  证明: by
  rcases isEmpty_or_nonempty ι
  · simp only [iUnion_of_empty, isSigmaCompact_empty]
  · -- If ι is non-empty, choose a surjection f : ℕ → ι, this yields a map ℕ → Set X.
    obtain ⟨f, hf⟩ := countable_iff_exists_surjective.mp hι
    exact ⟨s ∘ f, fun n => hcomp (f n), Function.Surjective.iUnion

Depends on / 依赖: Function, Function.Surjective.iUnion_comp, Surjective, countable_iff_exists_surjective, countable_iff_exists_surjective.mp, iUnion_comp, iUnion_of_empty, isEmpty_or_nonempty, isSigmaCompact_empty, surjection, yields
-/
lemma isSigmaCompact_iUnion_of_isCompact [hι : Countable ι] (s : ι -> Set X)
    (hcomp : forall i, IsCompact (s i)) : IsSigmaCompact (⋃ i, s i) := by
  rcases isEmpty_or_nonempty ι
  · simp only [iUnion_of_empty, isSigmaCompact_empty]
  · -- If ι is non-empty, choose a surjection f : ℕ → ι, this yields a map ℕ → Set X.
    obtain ⟨f, hf⟩ := countable_iff_exists_surjective.mp hι
    exact ⟨s ∘ f, fun n => hcomp (f n), Function.Surjective.iUnion_comp hf _⟩

/--
lemma `isSigmaCompact_sUnion_of_isCompact` / 引理 `isSigmaCompact_sUnion_of_isCompact`

English:
lemma isSigmaCompact_sUnion_of_isCompact
  statement: {S : Set (Set X)} (hc : Set.Countable S)
  proof: by
  have : Countable S := countable_coe_iff.mpr hc
  rw [sUnion_eq_iUnion]
  apply isSigmaCompact_iUnion_of_isCompact _ (fun ⟨s, hs⟩ => hcomp s hs)

中文:
引理 isSigmaCompact_sUnion_of_isCompact
  结论: {S : 集合 (集合 X)} (hc : 集合.可数 S)
  证明: by
  have : Countable S := countable_coe_iff.mpr hc
  rw [sUnion_eq_iUnion]
  apply isSigmaCompact_iUnion_of_isCompact _ (fun ⟨s, hs⟩ => hcomp s hs)

Depends on / 依赖: Countable, countable_coe_iff, countable_coe_iff.mpr, isSigmaCompact_iUnion_of_isCompact, sUnion_eq_iUnion
-/
lemma isSigmaCompact_sUnion_of_isCompact {S : Set (Set X)} (hc : Set.Countable S)
    (hcomp : forall (s : Set X), s in S -> IsCompact s) : IsSigmaCompact (⋃₀ S) := by
  have : Countable S := countable_coe_iff.mpr hc
  rw [sUnion_eq_iUnion]
  apply isSigmaCompact_iUnion_of_isCompact _ (fun ⟨s, hs⟩ => hcomp s hs)

/--
lemma `isSigmaCompact_iUnion` / 引理 `isSigmaCompact_iUnion`

English:
lemma isSigmaCompact_iUnion
  statement: [Countable ι] (s : ι -> Set X)
  proof: by
  -- Choose a decomposition s_i = ⋃ K_i,j for each i.
  choose K hcomp hcov using fun i => hcomp i
  -- Then, we have a countable union of countable unions of compact sets, i.e. countably many.
  have := calc
    ⋃ i, s i
    _ = ⋃ i, ⋃ n, (K i n) := by simp_rw [hcov]
    _ = ⋃ (i) (n : Nat), (K.

中文:
引理 isSigmaCompact_iUnion
  结论: [可数 ι] (s : ι -> 集合 X)
  证明: by
  -- Choose a decomposition s_i = ⋃ K_i,j for each i.
  choose K hcomp hcov using fun i => hcomp i
  -- Then, we have a countable union of countable unions of compact sets, i.e. countably many.
  have := calc
    ⋃ i, s i
    _ = ⋃ i, ⋃ n, (K i n) := by simp_rw [hcov]
    _ = ⋃ (i) (n : Nat), (K.
-/
lemma isSigmaCompact_iUnion [Countable ι] (s : ι -> Set X)
    (hcomp : forall i, IsSigmaCompact (s i)) : IsSigmaCompact (⋃ i, s i) := by
  -- Choose a decomposition s_i = ⋃ K_i,j for each i.
  choose K hcomp hcov using fun i => hcomp i
  -- Then, we have a countable union of countable unions of compact sets, i.e. countably many.
  have := calc
    ⋃ i, s i
    _ = ⋃ i, ⋃ n, (K i n) := by simp_rw [hcov]
    _ = ⋃ (i) (n : Nat), (K.uncurry ⟨i, n⟩) := by rw [Function.uncurry_def]
    _ = ⋃ x, K.uncurry x := by rw [← iUnion_prod']
  rw [this]
  exact isSigmaCompact_iUnion_of_isCompact K.uncurry fun x => (hcomp x.1 x.2)

/--
lemma `isSigmaCompact_sUnion` / 引理 `isSigmaCompact_sUnion`

English:
lemma isSigmaCompact_sUnion
  statement: (S : Set (Set X)) (hc : Set.Countable S)
  proof: by
  have : Countable S := countable_coe_iff.mpr hc
  apply sUnion_eq_iUnion.symm ▸ isSigmaCompact_iUnion _ hcomp

中文:
引理 isSigmaCompact_sUnion
  结论: (S : 集合 (集合 X)) (hc : 集合.可数 S)
  证明: by
  have : Countable S := countable_coe_iff.mpr hc
  apply sUnion_eq_iUnion.symm ▸ isSigmaCompact_iUnion _ hcomp

Depends on / 依赖: Countable, IsSigmaCompact, countable_coe_iff, countable_coe_iff.mpr, isSigmaCompact_iUnion, sUnion_eq_iUnion, sUnion_eq_iUnion.symm
-/
lemma isSigmaCompact_sUnion (S : Set (Set X)) (hc : Set.Countable S)
    (hcomp : forall s : S, IsSigmaCompact s (X := X)) : IsSigmaCompact (⋃₀ S) := by
  have : Countable S := countable_coe_iff.mpr hc
  apply sUnion_eq_iUnion.symm ▸ isSigmaCompact_iUnion _ hcomp

/--
lemma `isSigmaCompact_biUnion` / 引理 `isSigmaCompact_biUnion`

English:
lemma isSigmaCompact_biUnion
  statement: {s : Set ι} {S : ι -> Set X} (hc : Set.Countable s)
  proof: by
  have : Countable ↑s := countable_coe_iff.mpr hc
  rw [biUnion_eq_iUnion]
  exact isSigmaCompact_iUnion _ (fun ⟨i', hi'⟩ => hcomp i' hi')

中文:
引理 isSigmaCompact_biUnion
  结论: {s : 集合 ι} {S : ι -> 集合 X} (hc : 集合.可数 s)
  证明: by
  have : Countable ↑s := countable_coe_iff.mpr hc
  rw [biUnion_eq_iUnion]
  exact isSigmaCompact_iUnion _ (fun ⟨i', hi'⟩ => hcomp i' hi')

Depends on / 依赖: Countable, biUnion_eq_iUnion, countable_coe_iff, countable_coe_iff.mpr, isSigmaCompact_iUnion
-/
lemma isSigmaCompact_biUnion {s : Set ι} {S : ι -> Set X} (hc : Set.Countable s)
    (hcomp : forall (i : ι), i in s -> IsSigmaCompact (S i)) :
    IsSigmaCompact (⋃ (i : ι) (_ : i in s), S i) := by
  have : Countable ↑s := countable_coe_iff.mpr hc
  rw [biUnion_eq_iUnion]
  exact isSigmaCompact_iUnion _ (fun ⟨i', hi'⟩ => hcomp i' hi')

/--
lemma `IsSigmaCompact.of_isClosed_subset` / 引理 `IsSigmaCompact.of_isClosed_subset`

English:
lemma IsSigmaCompact.of_isClosed_subset
  statement: {s t : Set X} (ht : IsSigmaCompact t)
  proof: by
  rcases ht with ⟨K, hcompact, hcov⟩
  refine ⟨(fun n => s inter (K n)), fun n => (hcompact n).inter_left hs, ?_⟩
  rw [← inter_iUnion]; rw [hcov]
  exact inter_eq_left.mpr h

中文:
引理 IsSigmaCompact.of_isClosed_subset
  结论: {s t : 集合 X} (ht : IsSigmaCompact t)
  证明: by
  rcases ht with ⟨K, hcompact, hcov⟩
  refine ⟨(fun n => s inter (K n)), fun n => (hcompact n).inter_left hs, ?_⟩
  rw [← inter_iUnion]; rw [hcov]
  exact inter_eq_left.mpr h

Depends on / 依赖: hcompact, inter_eq_left, inter_eq_left.mpr, inter_iUnion, inter_left
-/
lemma IsSigmaCompact.of_isClosed_subset {s t : Set X} (ht : IsSigmaCompact t)
    (hs : IsClosed s) (h : s subseteq t) : IsSigmaCompact s := by
  rcases ht with ⟨K, hcompact, hcov⟩
  refine ⟨(fun n => s inter (K n)), fun n => (hcompact n).inter_left hs, ?_⟩
  rw [← inter_iUnion]; rw [hcov]
  exact inter_eq_left.mpr h

/--
lemma `IsSigmaCompact.image_of_continuousOn` / 引理 `IsSigmaCompact.image_of_continuousOn`

English:
lemma IsSigmaCompact.image_of_continuousOn
  statement: {f : X -> Y} {s : Set X} (hs : IsSigmaCompact s)
  proof: by
  rcases hs with ⟨K, hcompact, hcov⟩
  refine ⟨fun n => f '' K n, ?_, hcov.symm ▸ image_iUnion.symm⟩
  exact fun n => (hcompact n).image_of_continuousOn (hf.mono (hcov.symm ▸ subset_iUnion K n))

中文:
引理 IsSigmaCompact.image_of_continuousOn
  结论: {f : X -> Y} {s : 集合 X} (hs : IsSigmaCompact s)
  证明: by
  rcases hs with ⟨K, hcompact, hcov⟩
  refine ⟨fun n => f '' K n, ?_, hcov.symm ▸ image_iUnion.symm⟩
  exact fun n => (hcompact n).image_of_continuousOn (hf.mono (hcov.symm ▸ subset_iUnion K n))

Depends on / 依赖: hcompact, hcov.symm, hf.mono, image_iUnion, image_iUnion.symm, image_of_continuousOn, subset_iUnion
-/
lemma IsSigmaCompact.image_of_continuousOn {f : X -> Y} {s : Set X} (hs : IsSigmaCompact s)
    (hf : ContinuousOn f s) : IsSigmaCompact (f '' s) := by
  rcases hs with ⟨K, hcompact, hcov⟩
  refine ⟨fun n => f '' K n, ?_, hcov.symm ▸ image_iUnion.symm⟩
  exact fun n => (hcompact n).image_of_continuousOn (hf.mono (hcov.symm ▸ subset_iUnion K n))

/--
lemma `IsSigmaCompact.image` / 引理 `IsSigmaCompact.image`

English:
lemma IsSigmaCompact.image
  given: {f : X -> Y} (hf : Continuous f) {s : Set X} (hs : IsSigmaCompact s)
  proof: hs.image_of_continuousOn hf.continuousOn

中文:
引理 IsSigmaCompact.像
  条件: {f : X -> Y} (hf : 连续 f) {s : 集合 X} (hs : IsSigmaCompact s)
  证明: hs.image_of_continuousOn hf.continuousOn

Depends on / 依赖: continuousOn, hf.continuousOn, hs.image_of_continuousOn, image_of_continuousOn
-/
lemma IsSigmaCompact.image {f : X -> Y} (hf : Continuous f) {s : Set X} (hs : IsSigmaCompact s) :
    IsSigmaCompact (f '' s) := hs.image_of_continuousOn hf.continuousOn

/--
lemma `Topology.IsInducing.isSigmaCompact_iff` / 引理 `Topology.IsInducing.isSigmaCompact_iff`

English:
lemma Topology.IsInducing.isSigmaCompact_iff
  statement: {f : X -> Y} {s : Set X}
  proof: by
  constructor
  · exact fun h => h.image hf.continuous
  · rintro ⟨L, hcomp, hcov⟩
    -- Suppose f(s) is σ-compact; we want to show s is σ-compact.
    -- Write f(s) as a union of compact sets L n, so s = ⋃ K n with K n := f⁻¹(L n) ∩ s.
    -- Since f is inducing, each K n is compact iff L n is.

中文:
引理 拓扑.是Inducing.isSigmaCompact_iff
  结论: {f : X -> Y} {s : 集合 X}
  证明: by
  constructor
  · exact fun h => h.image hf.continuous
  · rintro ⟨L, hcomp, hcov⟩
    -- Suppose f(s) is σ-compact; we want to show s is σ-compact.
    -- Write f(s) as a union of compact sets L n, so s = ⋃ K n with K n := f⁻¹(L n) ∩ s.
    -- Since f is inducing, each K n is compact iff L n is.

Depends on / 依赖: continuous, h.image, hf.continuous
-/
lemma Topology.IsInducing.isSigmaCompact_iff {f : X -> Y} {s : Set X}
    (hf : IsInducing f) : IsSigmaCompact s ↔ IsSigmaCompact (f '' s) := by
  constructor
  · exact fun h => h.image hf.continuous
  · rintro ⟨L, hcomp, hcov⟩
    -- Suppose f(s) is σ-compact; we want to show s is σ-compact.
    -- Write f(s) as a union of compact sets L n, so s = ⋃ K n with K n := f⁻¹(L n) ∩ s.
    -- Since f is inducing, each K n is compact iff L n is.
    refine ⟨fun n => f ⁻¹' (L n) inter s, ?_, ?_⟩
    · intro n
      have : f '' (f ⁻¹' (L n) inter s) = L n := by
        rw [image_preimage_inter]; rw [inter_eq_left.mpr]
        exact (subset_iUnion _ n).trans hcov.le
      apply hf.isCompact_iff.mpr (this.symm ▸ (hcomp n))
    · calc ⋃ n, f ⁻¹' L n inter s
        _ = f ⁻¹' (⋃ n, L n) inter s := by rw [preimage_iUnion, iUnion_inter]
        _ = f ⁻¹' (f '' s) inter s := by rw [hcov]
        _ = s := inter_eq_right.mpr (subset_preimage_image _ _)

/--
lemma `Topology.IsEmbedding.isSigmaCompact_iff` / 引理 `Topology.IsEmbedding.isSigmaCompact_iff`

English:
lemma Topology.IsEmbedding.isSigmaCompact_iff
  statement: {f : X -> Y} {s : Set X}
  proof: hf.isInducing.isSigmaCompact_iff

中文:
引理 拓扑.是嵌入.isSigmaCompact_iff
  结论: {f : X -> Y} {s : 集合 X}
  证明: hf.isInducing.isSigmaCompact_iff

Depends on / 依赖: hf.isInducing.isSigmaCompact_iff, isInducing, isSigmaCompact_iff
-/
lemma Topology.IsEmbedding.isSigmaCompact_iff {f : X -> Y} {s : Set X}
    (hf : IsEmbedding f) : IsSigmaCompact s ↔ IsSigmaCompact (f '' s) :=
  hf.isInducing.isSigmaCompact_iff

/--
lemma `Subtype.isSigmaCompact_iff` / 引理 `Subtype.isSigmaCompact_iff`

English:
lemma Subtype.isSigmaCompact_iff
  given: {p : X -> Prop} {s : Set { a // p a }}
  proof: IsEmbedding.subtypeVal.isSigmaCompact_iff

中文:
引理 子类型.isSigmaCompact_iff
  条件: {p : X -> 命题} {s : 集合 { a // p a }}
  证明: IsEmbedding.subtypeVal.isSigmaCompact_iff

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.isSigmaCompact_iff, isSigmaCompact_iff, subtypeVal
-/
lemma Subtype.isSigmaCompact_iff {p : X -> Prop} {s : Set { a // p a }} :
    IsSigmaCompact s ↔ IsSigmaCompact ((↑) '' s : Set X) :=
  IsEmbedding.subtypeVal.isSigmaCompact_iff

/--
Definition of `SigmaCompactSpace` / `SigmaCompactSpace` 的定义

English:
class SigmaCompactSpace
  parameters: (X : Type*) [TopologicalSpace X]
  axioms and operations (1):
    - isSigmaCompact_univ : IsSigmaCompact (univ : Set X)

中文:
类 SigmaCompact空间
  参数: (X : 类型) [拓扑空间 X]
  公理与运算 (1 个):
    - isSigmaCompact_univ : IsSigmaCompact (univ : 集合 X)
-/
class SigmaCompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a σ-compact space, `Set.univ` is a σ-compact set. -/
  isSigmaCompact_univ : IsSigmaCompact (univ : Set X)

/--
lemma `isSigmaCompact_univ_iff` / 引理 `isSigmaCompact_univ_iff`

English:
lemma isSigmaCompact_univ_iff
  statement: IsSigmaCompact (univ : Set X) ↔ SigmaCompactSpace X
  proof: ⟨fun h => ⟨h⟩, fun h => h.1⟩

中文:
引理 isSigmaCompact_univ_iff
  结论: IsSigmaCompact (univ : 集合 X) ↔ SigmaCompact空间 X
  证明: ⟨fun h => ⟨h⟩, fun h => h.1⟩
-/
lemma isSigmaCompact_univ_iff : IsSigmaCompact (univ : Set X) ↔ SigmaCompactSpace X :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

/--
lemma `isSigmaCompact_univ` / 引理 `isSigmaCompact_univ`

English:
lemma isSigmaCompact_univ
  given: [h : SigmaCompactSpace X]
  statement: IsSigmaCompact (univ : Set X)
  proof: isSigmaCompact_univ_iff.mpr h

中文:
引理 isSigmaCompact_univ
  条件: [h : SigmaCompact空间 X]
  结论: IsSigmaCompact (univ : 集合 X)
  证明: isSigmaCompact_univ_iff.mpr h

Depends on / 依赖: isSigmaCompact_univ_iff, isSigmaCompact_univ_iff.mpr
-/
lemma isSigmaCompact_univ [h : SigmaCompactSpace X] : IsSigmaCompact (univ : Set X) :=
  isSigmaCompact_univ_iff.mpr h

/--
lemma `SigmaCompactSpace_iff_exists_compact_covering` / 引理 `SigmaCompactSpace_iff_exists_compact_covering`

English:
lemma SigmaCompactSpace_iff_exists_compact_covering
  proof: by
  rw [← isSigmaCompact_univ_iff]; rw [IsSigmaCompact]

中文:
引理 SigmaCompactSpace_iff_存在_compact_covering
  证明: by
  rw [← isSigmaCompact_univ_iff]; rw [IsSigmaCompact]

Depends on / 依赖: IsSigmaCompact, isSigmaCompact_univ_iff
-/
lemma SigmaCompactSpace_iff_exists_compact_covering :
    SigmaCompactSpace X ↔ exists K : Nat -> Set X, (forall n, IsCompact (K n)) ∧ ⋃ n, K n = univ := by
  rw [← isSigmaCompact_univ_iff]; rw [IsSigmaCompact]

/--
lemma `SigmaCompactSpace.exists_compact_covering` / 引理 `SigmaCompactSpace.exists_compact_covering`

English:
lemma SigmaCompactSpace.exists_compact_covering
  given: [h : SigmaCompactSpace X]
  proof: SigmaCompactSpace_iff_exists_compact_covering.mp h

中文:
引理 SigmaCompact空间.存在_compact_covering
  条件: [h : SigmaCompact空间 X]
  证明: SigmaCompactSpace_iff_exists_compact_covering.mp h

Depends on / 依赖: SigmaCompactSpace_iff_exists_compact_covering, SigmaCompactSpace_iff_exists_compact_covering.mp
-/
lemma SigmaCompactSpace.exists_compact_covering [h : SigmaCompactSpace X] :
    exists K : Nat -> Set X, (forall n, IsCompact (K n)) ∧ ⋃ n, K n = univ :=
  SigmaCompactSpace_iff_exists_compact_covering.mp h

/--
lemma `isSigmaCompact_range` / 引理 `isSigmaCompact_range`

English:
lemma isSigmaCompact_range
  given: {f : X -> Y} (hf : Continuous f) [SigmaCompactSpace X]
  proof: image_univ ▸ isSigmaCompact_univ.image hf

中文:
引理 isSigmaCompact_range
  条件: {f : X -> Y} (hf : 连续 f) [SigmaCompact空间 X]
  证明: image_univ ▸ isSigmaCompact_univ.image hf

Depends on / 依赖: image_univ, isSigmaCompact_univ, isSigmaCompact_univ.image
-/
lemma isSigmaCompact_range {f : X -> Y} (hf : Continuous f) [SigmaCompactSpace X] :
    IsSigmaCompact (range f) :=
  image_univ ▸ isSigmaCompact_univ.image hf

/--
lemma `isSigmaCompact_iff_isSigmaCompact_univ` / 引理 `isSigmaCompact_iff_isSigmaCompact_univ`

English:
lemma isSigmaCompact_iff_isSigmaCompact_univ
  given: {s : Set X}
  proof: by
  rw [Subtype.isSigmaCompact_iff]; rw [image_univ]; rw [Subtype.range_coe]

中文:
引理 isSigmaCompact_iff_isSigmaCompact_univ
  条件: {s : 集合 X}
  证明: by
  rw [Subtype.isSigmaCompact_iff]; rw [image_univ]; rw [Subtype.range_coe]

Depends on / 依赖: Subtype, Subtype.isSigmaCompact_iff, Subtype.range_coe, image_univ, isSigmaCompact_iff, range_coe
-/
lemma isSigmaCompact_iff_isSigmaCompact_univ {s : Set X} :
    IsSigmaCompact s ↔ IsSigmaCompact (univ : Set s) := by
  rw [Subtype.isSigmaCompact_iff]; rw [image_univ]; rw [Subtype.range_coe]

/--
lemma `isSigmaCompact_iff_sigmaCompactSpace` / 引理 `isSigmaCompact_iff_sigmaCompactSpace`

English:
lemma isSigmaCompact_iff_sigmaCompactSpace
  given: {s : Set X}
  proof: isSigmaCompact_iff_isSigmaCompact_univ.trans isSigmaCompact_univ_iff

中文:
引理 isSigmaCompact_iff_sigmaCompactSpace
  条件: {s : 集合 X}
  证明: isSigmaCompact_iff_isSigmaCompact_univ.trans isSigmaCompact_univ_iff

Depends on / 依赖: isSigmaCompact_iff_isSigmaCompact_univ, isSigmaCompact_iff_isSigmaCompact_univ.trans, isSigmaCompact_univ_iff
-/
lemma isSigmaCompact_iff_sigmaCompactSpace {s : Set X} :
    IsSigmaCompact s ↔ SigmaCompactSpace s :=
  isSigmaCompact_iff_isSigmaCompact_univ.trans isSigmaCompact_univ_iff

-- see Note [lower instance priority]
instance (priority := 200) CompactSpace.sigmaCompact [CompactSpace X] : SigmaCompactSpace X :=
  ⟨⟨fun _ => univ, fun _ => isCompact_univ, iUnion_const _⟩⟩

/--
theorem `SigmaCompactSpace.of_countable` / 定理 `SigmaCompactSpace.of_countable`

English:
theorem SigmaCompactSpace.of_countable
  statement: (S : Set (Set X)) (Hc : S.Countable)
  proof: ⟨(exists_seq_cover_iff_countable ⟨_, isCompact_empty⟩).2 ⟨S, Hc, Hcomp, HU⟩⟩

中文:
定理 SigmaCompact空间.of_countable
  结论: (S : 集合 (集合 X)) (Hc : S.可数)
  证明: ⟨(exists_seq_cover_iff_countable ⟨_, isCompact_empty⟩).2 ⟨S, Hc, Hcomp, HU⟩⟩

Depends on / 依赖: exists_seq_cover_iff_countable, isCompact_empty
-/
theorem SigmaCompactSpace.of_countable (S : Set (Set X)) (Hc : S.Countable)
    (Hcomp : forall s in S, IsCompact s) (HU : ⋃₀ S = univ) : SigmaCompactSpace X :=
  ⟨(exists_seq_cover_iff_countable ⟨_, isCompact_empty⟩).2 ⟨S, Hc, Hcomp, HU⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) sigmaCompactSpace_of_locallyCompact_secondCountable
    [LocallyCompactSpace X] [SecondCountableTopology X] : SigmaCompactSpace X := by
  choose K hKc hxK using fun x : X => exists_compact_mem_nhds x
  rcases countable_cover_nhds hxK with ⟨s, hsc, hsU⟩
  refine SigmaCompactSpace.of_countable _ (hsc.image K) (forall_mem_image.2 fun x _ => hKc x) ?_
  rwa [sUnion_image]

section

variable (X)
variable [SigmaCompactSpace X]

open SigmaCompactSpace

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `compactCovering` / `compactCovering` 的定义

English:
definition compactCovering
  signature: : Nat -> Set X
  body: accumulate exists_compact_covering.choose

中文:
定义 compactCovering
  签名: : 自然数 -> 集合 X
  定义体: accumulate exists_compact_covering.choose

Depends on / 依赖: accumulate, exists_compact_covering, exists_compact_covering.choose
-/
noncomputable def compactCovering : Nat -> Set X :=
  accumulate exists_compact_covering.choose

/--
theorem `isCompact_compactCovering` / 定理 `isCompact_compactCovering`

English:
theorem isCompact_compactCovering
  given: (n : Nat)
  statement: IsCompact (compactCovering X n)
  proof: isCompact_accumulate (Classical.choose_spec SigmaCompactSpace.exists_compact_covering).1 n

中文:
定理 isCompact_compactCovering
  条件: (n : 自然数)
  结论: 是紧集 (compactCovering X n)
  证明: isCompact_accumulate (Classical.choose_spec SigmaCompactSpace.exists_compact_covering).1 n

Depends on / 依赖: Classical, Classical.choose_spec, SigmaCompactSpace, SigmaCompactSpace.exists_compact_covering, choose_spec, exists_compact_covering, isCompact_accumulate
-/
theorem isCompact_compactCovering (n : Nat) : IsCompact (compactCovering X n) :=
  isCompact_accumulate (Classical.choose_spec SigmaCompactSpace.exists_compact_covering).1 n

/--
theorem `iUnion_compactCovering` / 定理 `iUnion_compactCovering`

English:
theorem iUnion_compactCovering
  statement: ⋃ n, compactCovering X n = univ
  proof: by
  rw [compactCovering]; rw [iUnion_accumulate]
  exact (Classical.choose_spec SigmaCompactSpace.exists_compact_covering).2

中文:
定理 iUnion_compactCovering
  结论: ⋃ n, compactCovering X n = univ
  证明: by
  rw [compactCovering]; rw [iUnion_accumulate]
  exact (Classical.choose_spec SigmaCompactSpace.exists_compact_covering).2

Depends on / 依赖: Classical, Classical.choose_spec, SigmaCompactSpace, SigmaCompactSpace.exists_compact_covering, choose_spec, compactCovering, exists_compact_covering, iUnion_accumulate
-/
theorem iUnion_compactCovering : ⋃ n, compactCovering X n = univ := by
  rw [compactCovering]; rw [iUnion_accumulate]
  exact (Classical.choose_spec SigmaCompactSpace.exists_compact_covering).2

/--
theorem `iUnion_closure_compactCovering` / 定理 `iUnion_closure_compactCovering`

English:
theorem iUnion_closure_compactCovering
  statement: ⋃ n, closure (compactCovering X n) = univ
  proof: eq_top_mono (iUnion_mono fun _ => subset_closure) (iUnion_compactCovering X)

@[mono, gcongr]

中文:
定理 iUnion_closure_compactCovering
  结论: ⋃ n, closure (compactCovering X n) = univ
  证明: eq_top_mono (iUnion_mono fun _ => subset_closure) (iUnion_compactCovering X)

@[mono, gcongr]

Depends on / 依赖: eq_top_mono, iUnion_compactCovering, iUnion_mono, subset_closure
-/
theorem iUnion_closure_compactCovering : ⋃ n, closure (compactCovering X n) = univ :=
  eq_top_mono (iUnion_mono fun _ => subset_closure) (iUnion_compactCovering X)

@[mono, gcongr]
/--
theorem `compactCovering_subset` / 定理 `compactCovering_subset`

English:
theorem compactCovering_subset
  given: ⦃m n
  statement: Nat⦄ (h : m <= n) : compactCovering X m subseteq compactCovering X n
  proof: monotone_accumulate h

中文:
定理 compactCovering_subset
  条件: ⦃m n
  结论: 自然数⦄ (h : m <= n) : compactCovering X m subseteq compactCovering X n
  证明: monotone_accumulate h

Depends on / 依赖: monotone_accumulate
-/
theorem compactCovering_subset ⦃m n : Nat⦄ (h : m <= n) : compactCovering X m subseteq compactCovering X n :=
  monotone_accumulate h

variable {X}

/--
theorem `exists_mem_compactCovering` / 定理 `exists_mem_compactCovering`

English:
theorem exists_mem_compactCovering
  given: (x : X)
  statement: exists n, x in compactCovering X n
  proof: iUnion_eq_univ_iff.mp (iUnion_compactCovering X) x

中文:
定理 存在_mem_compactCovering
  条件: (x : X)
  结论: 存在 n, x in compactCovering X n
  证明: iUnion_eq_univ_iff.mp (iUnion_compactCovering X) x

Depends on / 依赖: iUnion_compactCovering, iUnion_eq_univ_iff, iUnion_eq_univ_iff.mp
-/
theorem exists_mem_compactCovering (x : X) : exists n, x in compactCovering X n :=
  iUnion_eq_univ_iff.mp (iUnion_compactCovering X) x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SigmaCompactSpace
  signature: Y] : SigmaCompactSpace (X × Y)
  body: ⟨⟨fun n => compactCovering X n ×ˢ compactCovering Y n, fun _ =>
      (isCompact_compactCovering _ _).prod (isCompact_compactCovering _ _), by
      simp only [iUnion_prod_of_monotone (compactCovering_subset X) (compactCovering_subset Y),
        iUnion_compactCovering, univ_prod_univ]⟩⟩

中文:
实例 [SigmaCompact空间
  签名: Y] : SigmaCompact空间 (X × Y)
  定义体: ⟨⟨fun n => compactCovering X n ×ˢ compactCovering Y n, fun _ =>
      (isCompact_compactCovering _ _).prod (isCompact_compactCovering _ _), by
      simp only [iUnion_prod_of_monotone (compactCovering_subset X) (compactCovering_subset Y),
        iUnion_compactCovering, univ_prod_univ]⟩⟩

Depends on / 依赖: compactCovering, compactCovering_subset, iUnion_compactCovering, iUnion_prod_of_monotone, isCompact_compactCovering, univ_prod_univ
-/
instance [SigmaCompactSpace Y] : SigmaCompactSpace (X × Y) :=
  ⟨⟨fun n => compactCovering X n ×ˢ compactCovering Y n, fun _ =>
      (isCompact_compactCovering _ _).prod (isCompact_compactCovering _ _), by
      simp only [iUnion_prod_of_monotone (compactCovering_subset X) (compactCovering_subset Y),
        iUnion_compactCovering, univ_prod_univ]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: ι] {X
  body: by
  refine ⟨⟨fun n => Set.pi univ fun i => compactCovering (X i) n,
    fun n => isCompact_univ_pi fun i => isCompact_compactCovering (X i) _, ?_⟩⟩
  rw [iUnion_univ_pi_of_monotone]
  · simp only [iUnion_compactCovering, pi_univ]
  · exact fun i => compactCovering_subset (X i)

中文:
实例 [有限
  签名: ι] {X
  定义体: by
  refine ⟨⟨fun n => Set.pi univ fun i => compactCovering (X i) n,
    fun n => isCompact_univ_pi fun i => isCompact_compactCovering (X i) _, ?_⟩⟩
  rw [iUnion_univ_pi_of_monotone]
  · simp only [iUnion_compactCovering, pi_univ]
  · exact fun i => compactCovering_subset (X i)

Depends on / 依赖: Set.pi, compactCovering, compactCovering_subset, iUnion_compactCovering, iUnion_univ_pi_of_monotone, isCompact_compactCovering, isCompact_univ_pi, pi_univ
-/
instance [Finite ι] {X : ι -> Type*} [forall i, TopologicalSpace (X i)] [forall i, SigmaCompactSpace (X i)] :
    SigmaCompactSpace (forall i, X i) := by
  refine ⟨⟨fun n => Set.pi univ fun i => compactCovering (X i) n,
    fun n => isCompact_univ_pi fun i => isCompact_compactCovering (X i) _, ?_⟩⟩
  rw [iUnion_univ_pi_of_monotone]
  · simp only [iUnion_compactCovering, pi_univ]
  · exact fun i => compactCovering_subset (X i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SigmaCompactSpace
  signature: Y] : SigmaCompactSpace (X oplus Y)
  body: ⟨⟨fun n => Sum.inl '' compactCovering X n union Sum.inr '' compactCovering Y n, fun n =>
      ((isCompact_compactCovering X n).image continuous_inl).union
        ((isCompact_compactCovering Y n).image continuous_inr),
      by simp only [iUnion_union_distrib, ← image_iUnion, iUnion_compactCovering

中文:
实例 [SigmaCompact空间
  签名: Y] : SigmaCompact空间 (X oplus Y)
  定义体: ⟨⟨fun n => Sum.inl '' compactCovering X n union Sum.inr '' compactCovering Y n, fun n =>
      ((isCompact_compactCovering X n).image continuous_inl).union
        ((isCompact_compactCovering Y n).image continuous_inr),
      by simp only [iUnion_union_distrib, ← image_iUnion, iUnion_compactCovering

Depends on / 依赖: Sum.inl, Sum.inr, compactCovering, continuous_inl, continuous_inr, iUnion_compactCovering, iUnion_union_distrib, image_iUnion, image_univ, isCompact_compactCovering, range_inl_union_range_inr
-/
instance [SigmaCompactSpace Y] : SigmaCompactSpace (X oplus Y) :=
  ⟨⟨fun n => Sum.inl '' compactCovering X n union Sum.inr '' compactCovering Y n, fun n =>
      ((isCompact_compactCovering X n).image continuous_inl).union
        ((isCompact_compactCovering Y n).image continuous_inr),
      by simp only [iUnion_union_distrib, ← image_iUnion, iUnion_compactCovering, image_univ,
        range_inl_union_range_inr]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Countable
  signature: ι] {X
  body: by
  cases isEmpty_or_nonempty ι
  · infer_instance
  · rcases exists_surjective_nat ι with ⟨f, hf⟩
    refine ⟨⟨fun n => ⋃ k <= n, Sigma.mk (f k) '' compactCovering (X (f k)) n, fun n => ?_, ?_⟩⟩
    · refine (finite_le_nat _).isCompact_biUnion fun k _ => ?_
      exact (isCompact_compactCovering _

中文:
实例 [可数
  签名: ι] {X
  定义体: by
  cases isEmpty_or_nonempty ι
  · infer_instance
  · rcases exists_surjective_nat ι with ⟨f, hf⟩
    refine ⟨⟨fun n => ⋃ k <= n, Sigma.mk (f k) '' compactCovering (X (f k)) n, fun n => ?_, ?_⟩⟩
    · refine (finite_le_nat _).isCompact_biUnion fun k _ => ?_
      exact (isCompact_compactCovering _

Depends on / 依赖: Sigma.forall, Sigma.mk, compactCovering, continuous_sigmaMk, exists_mem_compactCovering, exists_surjective_nat, finite_le_nat, hf.forall, iUnion_eq_univ_iff, infer_instance, isCompact_biUnion, isCompact_compactCovering, isEmpty_or_nonempty, le_max_left, mem_iUnion, mem_image_of_mem
-/
instance [Countable ι] {X : ι -> Type*} [forall i, TopologicalSpace (X i)]
    [forall i, SigmaCompactSpace (X i)] : SigmaCompactSpace (Σ i, X i) := by
  cases isEmpty_or_nonempty ι
  · infer_instance
  · rcases exists_surjective_nat ι with ⟨f, hf⟩
    refine ⟨⟨fun n => ⋃ k <= n, Sigma.mk (f k) '' compactCovering (X (f k)) n, fun n => ?_, ?_⟩⟩
    · refine (finite_le_nat _).isCompact_biUnion fun k _ => ?_
      exact (isCompact_compactCovering _ _).image continuous_sigmaMk
    · simp only [iUnion_eq_univ_iff, Sigma.forall, mem_iUnion, hf.forall]
      intro k y
      rcases exists_mem_compactCovering y with ⟨n, hn⟩
      refine ⟨max k n, k, le_max_left _ _, mem_image_of_mem _ ?_⟩
      exact compactCovering_subset _ (le_max_right _ _) hn

/--
lemma `Topology.IsClosedEmbedding.sigmaCompactSpace` / 引理 `Topology.IsClosedEmbedding.sigmaCompactSpace`

English:
lemma Topology.IsClosedEmbedding.sigmaCompactSpace
  statement: {e : Y -> X}
  proof: ⟨⟨fun n => e ⁻¹' compactCovering X n, fun _ =>
      he.isCompact_preimage (isCompact_compactCovering _ _), by
      rw [← preimage_iUnion]; rw [iUnion_compactCovering]; rw [preimage_univ]⟩⟩

中文:
引理 拓扑.是闭嵌入.sigmaCompactSpace
  结论: {e : Y -> X}
  证明: ⟨⟨fun n => e ⁻¹' compactCovering X n, fun _ =>
      he.isCompact_preimage (isCompact_compactCovering _ _), by
      rw [← preimage_iUnion]; rw [iUnion_compactCovering]; rw [preimage_univ]⟩⟩
-/
protected lemma Topology.IsClosedEmbedding.sigmaCompactSpace {e : Y -> X}
    (he : IsClosedEmbedding e) : SigmaCompactSpace Y :=
  ⟨⟨fun n => e ⁻¹' compactCovering X n, fun _ =>
      he.isCompact_preimage (isCompact_compactCovering _ _), by
      rw [← preimage_iUnion]; rw [iUnion_compactCovering]; rw [preimage_univ]⟩⟩

/--
theorem `IsClosed.sigmaCompactSpace` / 定理 `IsClosed.sigmaCompactSpace`

English:
theorem IsClosed.sigmaCompactSpace
  given: {s : Set X} (hs : IsClosed s)
  statement: SigmaCompactSpace s
  proof: hs.isClosedEmbedding_subtypeVal.sigmaCompactSpace

中文:
定理 是闭集.sigmaCompactSpace
  条件: {s : 集合 X} (hs : 是闭集 s)
  结论: SigmaCompact空间 s
  证明: hs.isClosedEmbedding_subtypeVal.sigmaCompactSpace

Depends on / 依赖: hs.isClosedEmbedding_subtypeVal.sigmaCompactSpace, isClosedEmbedding_subtypeVal, sigmaCompactSpace
-/
theorem IsClosed.sigmaCompactSpace {s : Set X} (hs : IsClosed s) : SigmaCompactSpace s :=
  hs.isClosedEmbedding_subtypeVal.sigmaCompactSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SigmaCompactSpace
  signature: Y] : SigmaCompactSpace (ULift.{u} Y)
  body: IsClosedEmbedding.uliftDown.sigmaCompactSpace

中文:
实例 [SigmaCompact空间
  签名: Y] : SigmaCompact空间 (类型层提升.{u} Y)
  定义体: IsClosedEmbedding.uliftDown.sigmaCompactSpace

Depends on / 依赖: IsClosedEmbedding, IsClosedEmbedding.uliftDown.sigmaCompactSpace, sigmaCompactSpace, uliftDown
-/
instance [SigmaCompactSpace Y] : SigmaCompactSpace (ULift.{u} Y) :=
  IsClosedEmbedding.uliftDown.sigmaCompactSpace

/--
theorem `LocallyFinite.countable_univ` / 定理 `LocallyFinite.countable_univ`

English:
theorem LocallyFinite.countable_univ
  statement: {f : ι -> Set X} (hf : LocallyFinite f)
  proof: by
  have := fun n => hf.finite_nonempty_inter_compact (isCompact_compactCovering X n)
  refine (countable_iUnion fun n => (this n).countable).mono fun i _ => ?_
  rcases hne i with ⟨x, hx⟩
  rcases iUnion_eq_univ_iff.1 (iUnion_compactCovering X) x with ⟨n, hn⟩
  exact mem_iUnion.2 ⟨n, x, hx, hn⟩

中文:
定理 局部有限.countable_univ
  结论: {f : ι -> 集合 X} (hf : 局部有限 f)
  证明: by
  have := fun n => hf.finite_nonempty_inter_compact (isCompact_compactCovering X n)
  refine (countable_iUnion fun n => (this n).countable).mono fun i _ => ?_
  rcases hne i with ⟨x, hx⟩
  rcases iUnion_eq_univ_iff.1 (iUnion_compactCovering X) x with ⟨n, hn⟩
  exact mem_iUnion.2 ⟨n, x, hx, hn⟩
-/
protected theorem LocallyFinite.countable_univ {f : ι -> Set X} (hf : LocallyFinite f)
    (hne : forall i, (f i).Nonempty) : (univ : Set ι).Countable := by
  have := fun n => hf.finite_nonempty_inter_compact (isCompact_compactCovering X n)
  refine (countable_iUnion fun n => (this n).countable).mono fun i _ => ?_
  rcases hne i with ⟨x, hx⟩
  rcases iUnion_eq_univ_iff.1 (iUnion_compactCovering X) x with ⟨n, hn⟩
  exact mem_iUnion.2 ⟨n, x, hx, hn⟩

/-- If `f : ι → Set X` is a locally finite covering of a σ-compact topological space by nonempty
sets, then the index type `ι` is encodable. -/
@[instance_reducible]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def LocallyFinite.encodable {ι : Type*} {f : ι -> Set X}
  body: @Encodable.ofEquiv _ _ (hf.countable_univ hne).toEncodable (Equiv.Set.univ _).symm

中文:
定义 noncomputable
  签名: def 局部有限.encodable {ι : 类型} {f : ι -> 集合 X}
  定义体: @Encodable.ofEquiv _ _ (hf.countable_univ hne).toEncodable (Equiv.Set.univ _).symm
-/
protected noncomputable def LocallyFinite.encodable {ι : Type*} {f : ι -> Set X}
    (hf : LocallyFinite f) (hne : forall i, (f i).Nonempty) : Encodable ι :=
  @Encodable.ofEquiv _ _ (hf.countable_univ hne).toEncodable (Equiv.Set.univ _).symm

/--
theorem `countable_cover_nhdsWithin_of_sigmaCompact` / 定理 `countable_cover_nhdsWithin_of_sigmaCompact`

English:
theorem countable_cover_nhdsWithin_of_sigmaCompact
  statement: {f : X -> Set X} {s : Set X} (hs : IsClosed s)
  proof: by
  simp only [nhdsWithin, mem_inf_principal] at hf
  choose t ht hsub using fun n =>
    ((isCompact_compactCovering X n).inter_right hs).elim_nhds_subcover _ fun x hx => hf x hx.right
  refine
    ⟨⋃ n, (t n : Set X), iUnion_subset fun n x hx => (ht n x hx).2,
      countable_iUnion fun n => (t n

中文:
定理 countable_cover_nhdsWithin_of_sigmaCompact
  结论: {f : X -> 集合 X} {s : 集合 X} (hs : 是闭集 s)
  证明: by
  simp only [nhdsWithin, mem_inf_principal] at hf
  choose t ht hsub using fun n =>
    ((isCompact_compactCovering X n).inter_right hs).elim_nhds_subcover _ fun x hx => hf x hx.right
  refine
    ⟨⋃ n, (t n : Set X), iUnion_subset fun n x hx => (ht n x hx).2,
      countable_iUnion fun n => (t n

Depends on / 依赖: countable_iUnion, countable_toSet, elim_nhds_subcover, exists_mem_compactCovering, hx.right, iUnion_subset, inter_right, isCompact_compactCovering, mem_iUnion, mem_inf_principal, nhdsWithin
-/
theorem countable_cover_nhdsWithin_of_sigmaCompact {f : X -> Set X} {s : Set X} (hs : IsClosed s)
    (hf : forall x in s, f x in 𝓝[s] x) : exists t subseteq s, t.Countable ∧ s subseteq ⋃ x in t, f x := by
  simp only [nhdsWithin, mem_inf_principal] at hf
  choose t ht hsub using fun n =>
    ((isCompact_compactCovering X n).inter_right hs).elim_nhds_subcover _ fun x hx => hf x hx.right
  refine
    ⟨⋃ n, (t n : Set X), iUnion_subset fun n x hx => (ht n x hx).2,
      countable_iUnion fun n => (t n).countable_toSet, fun x hx => mem_iUnion₂.2 ?_⟩
  rcases exists_mem_compactCovering x with ⟨n, hn⟩
  rcases mem_iUnion₂.1 (hsub n ⟨hn, hx⟩) with ⟨y, hyt : y in t n, hyf : x in s -> x in f y⟩
  exact ⟨y, mem_iUnion.2 ⟨n, hyt⟩, hyf hx⟩

/--
theorem `countable_cover_nhds_of_sigmaCompact` / 定理 `countable_cover_nhds_of_sigmaCompact`

English:
theorem countable_cover_nhds_of_sigmaCompact
  given: {f : X -> Set X} (hf : forall x, f x in 𝓝 x)
  proof: by
  simp only [← nhdsWithin_univ] at hf
  rcases countable_cover_nhdsWithin_of_sigmaCompact isClosed_univ fun x _ => hf x with
    ⟨s, -, hsc, hsU⟩
  exact ⟨s, hsc, univ_subset_iff.1 hsU⟩

中文:
定理 countable_cover_nhds_of_sigmaCompact
  条件: {f : X -> 集合 X} (hf : 对任意 x, f x in 𝓝 x)
  证明: by
  simp only [← nhdsWithin_univ] at hf
  rcases countable_cover_nhdsWithin_of_sigmaCompact isClosed_univ fun x _ => hf x with
    ⟨s, -, hsc, hsU⟩
  exact ⟨s, hsc, univ_subset_iff.1 hsU⟩

Depends on / 依赖: countable_cover_nhdsWithin_of_sigmaCompact, isClosed_univ, nhdsWithin_univ, univ_subset_iff
-/
theorem countable_cover_nhds_of_sigmaCompact {f : X -> Set X} (hf : forall x, f x in 𝓝 x) :
    exists s : Set X, s.Countable ∧ ⋃ x in s, f x = univ := by
  simp only [← nhdsWithin_univ] at hf
  rcases countable_cover_nhdsWithin_of_sigmaCompact isClosed_univ fun x _ => hf x with
    ⟨s, -, hsc, hsU⟩
  exact ⟨s, hsc, univ_subset_iff.1 hsU⟩
end

/--
Definition of `CompactExhaustion` / `CompactExhaustion` 的定义

English:
structure CompactExhaustion
  parameters: (X : Type*) [TopologicalSpace X]
  axioms and operations (4):
    - toFun : Nat -> Set X
    - isCompact' : forall n, IsCompact (toFun n)
    - subset_interior_succ' : forall n, toFun n subseteq interior (toFun (n + 1))
    - iUnion_eq' : ⋃ n, toFun n = univ

中文:
结构 余mpactExhaustion
  参数: (X : 类型) [拓扑空间 X]
  公理与运算 (4 个):
    - toFun : 自然数 -> 集合 X
    - isCompact' : 对任意 n, 是紧集 (toFun n)
    - subset_interior_succ' : 对任意 n, toFun n subseteq interior (toFun (n + 1))
    - iUnion_eq' : ⋃ n, toFun n = univ
-/
structure CompactExhaustion (X : Type*) [TopologicalSpace X] where
  /-- The sequence of compact sets that form a compact exhaustion. -/
  toFun : Nat -> Set X
  /-- The sets in the compact exhaustion are in fact compact. -/
  isCompact' : forall n, IsCompact (toFun n)
  /-- The sets in the compact exhaustion form a sequence:
  each set is contained in the interior of the next. -/
  subset_interior_succ' : forall n, toFun n subseteq interior (toFun (n + 1))
  /-- The union of all sets in a compact exhaustion equals the entire space. -/
  iUnion_eq' : ⋃ n, toFun n = univ

namespace CompactExhaustion

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (CompactExhaustion X) Nat (Set X)
  body: toFun
  coe_injective | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

中文:
实例 :
  签名: 函数状 (余mpactExhaustion X) 自然数 (集合 X)
  定义体: toFun
  coe_injective | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl
-/
instance : FunLike (CompactExhaustion X) Nat (Set X) where
  coe := toFun
  coe_injective | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderHomClass (CompactExhaustion X) Nat (Set X)
  body: monotone_nat_of_le_succ
    (fun n => (f.subset_interior_succ' n).trans interior_subset) h

中文:
实例 :
  签名: 序态射类 (余mpactExhaustion X) 自然数 (集合 X)
  定义体: monotone_nat_of_le_succ
    (fun n => (f.subset_interior_succ' n).trans interior_subset) h

Depends on / 依赖: monotone_nat_of_le_succ
-/
instance : OrderHomClass (CompactExhaustion X) Nat (Set X) where
  map_rel f _ _ h := monotone_nat_of_le_succ
    (fun n => (f.subset_interior_succ' n).trans interior_subset) h

variable (K : CompactExhaustion X)

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  statement: K.toFun = K
  proof: rfl

中文:
定理 toFun_eq_coe
  结论: K.toFun = K
  证明: rfl
-/
theorem toFun_eq_coe : K.toFun = K := rfl

/--
theorem `isCompact` / 定理 `isCompact`

English:
theorem isCompact
  given: (n : Nat)
  statement: IsCompact (K n)
  proof: K.isCompact' n

中文:
定理 isCompact
  条件: (n : 自然数)
  结论: 是紧集 (K n)
  证明: K.isCompact' n
-/
protected theorem isCompact (n : Nat) : IsCompact (K n) :=
  K.isCompact' n

/--
theorem `subset_interior_succ` / 定理 `subset_interior_succ`

English:
theorem subset_interior_succ
  given: (n : Nat)
  statement: K n subseteq interior (K (n + 1))
  proof: K.subset_interior_succ' n

@[gcongr, mono]

中文:
定理 subset_interior_succ
  条件: (n : 自然数)
  结论: K n subseteq interior (K (n + 1))
  证明: K.subset_interior_succ' n

@[gcongr, mono]

Depends on / 依赖: K.subset_interior_succ, subset_interior_succ
-/
theorem subset_interior_succ (n : Nat) : K n subseteq interior (K (n + 1)) :=
  K.subset_interior_succ' n

@[gcongr, mono]
/--
theorem `subset` / 定理 `subset`

English:
theorem subset
  given: ⦃m n
  statement: Nat⦄ (h : m <= n) : K m subseteq K n
  proof: OrderHomClass.mono K h

中文:
定理 subset
  条件: ⦃m n
  结论: 自然数⦄ (h : m <= n) : K m subseteq K n
  证明: OrderHomClass.mono K h
-/
protected theorem subset ⦃m n : Nat⦄ (h : m <= n) : K m subseteq K n :=
  OrderHomClass.mono K h

/--
theorem `subset_succ` / 定理 `subset_succ`

English:
theorem subset_succ
  given: (n : Nat)
  statement: K n subseteq K (n + 1)
  proof: K.subset n.le_succ

中文:
定理 subset_succ
  条件: (n : 自然数)
  结论: K n subseteq K (n + 1)
  证明: K.subset n.le_succ

Depends on / 依赖: K.subset, le_succ, n.le_succ, subset
-/
theorem subset_succ (n : Nat) : K n subseteq K (n + 1) := K.subset n.le_succ

/--
theorem `subset_interior` / 定理 `subset_interior`

English:
theorem subset_interior
  given: ⦃m n
  statement: Nat⦄ (h : m < n) : K m subseteq interior (K n)
  proof: Subset.trans (K.subset_interior_succ m) interior_mono K.subset h

中文:
定理 subset_interior
  条件: ⦃m n
  结论: 自然数⦄ (h : m < n) : K m subseteq interior (K n)
  证明: Subset.trans (K.subset_interior_succ m) interior_mono K.subset h

Depends on / 依赖: K.subset, K.subset_interior_succ, Subset, Subset.trans, interior_mono, subset, subset_interior_succ
-/
theorem subset_interior ⦃m n : Nat⦄ (h : m < n) : K m subseteq interior (K n) :=
Subset.trans (K.subset_interior_succ m) interior_mono K.subset h

/--
theorem `iUnion_eq` / 定理 `iUnion_eq`

English:
theorem iUnion_eq
  statement: ⋃ n, K n = univ
  proof: K.iUnion_eq'

中文:
定理 iUnion_eq
  结论: ⋃ n, K n = univ
  证明: K.iUnion_eq'

Depends on / 依赖: K.iUnion_eq, iUnion_eq
-/
theorem iUnion_eq : ⋃ n, K n = univ :=
  K.iUnion_eq'

/--
theorem `exists_mem` / 定理 `exists_mem`

English:
theorem exists_mem
  given: (x : X)
  statement: exists n, x in K n
  proof: iUnion_eq_univ_iff.1 K.iUnion_eq x

中文:
定理 存在_mem
  条件: (x : X)
  结论: 存在 n, x in K n
  证明: iUnion_eq_univ_iff.1 K.iUnion_eq x

Depends on / 依赖: K.iUnion_eq, iUnion_eq, iUnion_eq_univ_iff
-/
theorem exists_mem (x : X) : exists n, x in K n :=
  iUnion_eq_univ_iff.1 K.iUnion_eq x

/--
theorem `exists_mem_nhds` / 定理 `exists_mem_nhds`

English:
theorem exists_mem_nhds
  given: (x : X)
  statement: exists n, K n in 𝓝 x
  proof: by
  rcases K.exists_mem x with ⟨n, hn⟩
exact ⟨n + 1, mem_interior_iff_mem_nhds.mp K.subset_interior_succ n hn⟩

中文:
定理 存在_mem_nhds
  条件: (x : X)
  结论: 存在 n, K n in 𝓝 x
  证明: by
  rcases K.exists_mem x with ⟨n, hn⟩
exact ⟨n + 1, mem_interior_iff_mem_nhds.mp K.subset_interior_succ n hn⟩

Depends on / 依赖: K.exists_mem, K.subset_interior_succ, exists_mem, mem_interior_iff_mem_nhds, mem_interior_iff_mem_nhds.mp, subset_interior_succ
-/
theorem exists_mem_nhds (x : X) : exists n, K n in 𝓝 x := by
  rcases K.exists_mem x with ⟨n, hn⟩
exact ⟨n + 1, mem_interior_iff_mem_nhds.mp K.subset_interior_succ n hn⟩

/--
theorem `exists_superset_of_isCompact` / 定理 `exists_superset_of_isCompact`

English:
theorem exists_superset_of_isCompact
  given: {s : Set X} (hs : IsCompact s)
  statement: exists n, s subseteq K n
  proof: by
  suffices exists n, s subseteq interior (K n) from this.imp fun _ => (Subset.trans · interior_subset)
  refine hs.elim_directed_cover (interior ∘ K) (fun _ => isOpen_interior) ?_ ?_
  · intro x _
    rcases K.exists_mem x with ⟨k, hk⟩
    exact mem_iUnion.2 ⟨k + 1, K.subset_interior_succ _ hk⟩
·

中文:
定理 存在_superset_of_isCompact
  条件: {s : 集合 X} (hs : 是紧集 s)
  结论: 存在 n, s subseteq K n
  证明: by
  suffices exists n, s subseteq interior (K n) from this.imp fun _ => (Subset.trans · interior_subset)
  refine hs.elim_directed_cover (interior ∘ K) (fun _ => isOpen_interior) ?_ ?_
  · intro x _
    rcases K.exists_mem x with ⟨k, hk⟩
    exact mem_iUnion.2 ⟨k + 1, K.subset_interior_succ _ hk⟩
·

Depends on / 依赖: K.exists_mem, K.subset, K.subset_interior_succ, Monotone, Monotone.directed_le, Subset, Subset.trans, directed_le, elim_directed_cover, exists_mem, hs.elim_directed_cover, interior, interior_mono, interior_subset, isOpen_interior, mem_iUnion, subset, subset_interior_succ, subseteq, this.imp
-/
theorem exists_superset_of_isCompact {s : Set X} (hs : IsCompact s) : exists n, s subseteq K n := by
  suffices exists n, s subseteq interior (K n) from this.imp fun _ => (Subset.trans · interior_subset)
  refine hs.elim_directed_cover (interior ∘ K) (fun _ => isOpen_interior) ?_ ?_
  · intro x _
    rcases K.exists_mem x with ⟨k, hk⟩
    exact mem_iUnion.2 ⟨k + 1, K.subset_interior_succ _ hk⟩
· exact Monotone.directed_le fun _ _ h => interior_mono K.subset h

open scoped Classical in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def find (x : X)
  body: Nat.find (K.exists_mem x)

中文:
定义 noncomputable
  签名: def find (x : X)
  定义体: Nat.find (K.exists_mem x)
-/
protected noncomputable def find (x : X) : Nat :=
  Nat.find (K.exists_mem x)

/--
theorem `mem_find` / 定理 `mem_find`

English:
theorem mem_find
  given: (x : X)
  statement: x in K (K.find x)
  proof: by
  classical
  exact Nat.find_spec (K.exists_mem x)

中文:
定理 mem_find
  条件: (x : X)
  结论: x in K (K.find x)
  证明: by
  classical
  exact Nat.find_spec (K.exists_mem x)

Depends on / 依赖: K.exists_mem, Nat.find_spec, classical, exists_mem, find_spec
-/
theorem mem_find (x : X) : x in K (K.find x) := by
  classical
  exact Nat.find_spec (K.exists_mem x)

/--
theorem `mem_iff_find_le` / 定理 `mem_iff_find_le`

English:
theorem mem_iff_find_le
  given: {x : X} {n : Nat}
  statement: x in K n ↔ K.find x <= n
  proof: by
  classical
exact ⟨fun h => Nat.find_min' (K.exists_mem x) h, fun h => K.subset h K.mem_find x⟩

中文:
定理 mem_iff_find_le
  条件: {x : X} {n : 自然数}
  结论: x in K n ↔ K.find x <= n
  证明: by
  classical
exact ⟨fun h => Nat.find_min' (K.exists_mem x) h, fun h => K.subset h K.mem_find x⟩

Depends on / 依赖: K.exists_mem, K.mem_find, K.subset, Nat.find_min, classical, exists_mem, find_min, mem_find, subset
-/
theorem mem_iff_find_le {x : X} {n : Nat} : x in K n ↔ K.find x <= n := by
  classical
exact ⟨fun h => Nat.find_min' (K.exists_mem x) h, fun h => K.subset h K.mem_find x⟩

/--
Definition of `shiftr` / `shiftr` 的定义

English:
definition shiftr
  signature: : CompactExhaustion X where
  body: Nat.casesOn n ∅ K
  isCompact' n := Nat.casesOn n isCompact_empty K.isCompact
  subset_interior_succ' n := Nat.casesOn n (empty_subset _) K.subset_interior_succ
  iUnion_eq' := iUnion_eq_univ_iff.2 fun x => ⟨K.find x + 1, K.mem_find x⟩

@[simp]

中文:
定义 shiftr
  签名: : 余mpactExhaustion X where
  定义体: Nat.casesOn n ∅ K
  isCompact' n := Nat.casesOn n isCompact_empty K.isCompact
  subset_interior_succ' n := Nat.casesOn n (empty_subset _) K.subset_interior_succ
  iUnion_eq' := iUnion_eq_univ_iff.2 fun x => ⟨K.find x + 1, K.mem_find x⟩

@[simp]

Depends on / 依赖: Nat.casesOn, casesOn
-/
def shiftr : CompactExhaustion X where
  toFun n := Nat.casesOn n ∅ K
  isCompact' n := Nat.casesOn n isCompact_empty K.isCompact
  subset_interior_succ' n := Nat.casesOn n (empty_subset _) K.subset_interior_succ
  iUnion_eq' := iUnion_eq_univ_iff.2 fun x => ⟨K.find x + 1, K.mem_find x⟩

@[simp]
/--
theorem `find_shiftr` / 定理 `find_shiftr`

English:
theorem find_shiftr
  given: (x : X)
  statement: K.shiftr.find x = K.find x + 1
  proof: by
  classical
  exact Nat.find_comp_succ _ _ (notMem_empty _)

中文:
定理 find_shiftr
  条件: (x : X)
  结论: K.shiftr.find x = K.find x + 1
  证明: by
  classical
  exact Nat.find_comp_succ _ _ (notMem_empty _)

Depends on / 依赖: Nat.find_comp_succ, classical, find_comp_succ, notMem_empty
-/
theorem find_shiftr (x : X) : K.shiftr.find x = K.find x + 1 := by
  classical
  exact Nat.find_comp_succ _ _ (notMem_empty _)

/--
theorem `mem_sdiff_shiftr_find` / 定理 `mem_sdiff_shiftr_find`

English:
theorem mem_sdiff_shiftr_find
  given: (x : X)
  statement: x in K.shiftr (K.find x + 1) \ K.shiftr (K.find x)
  proof: ⟨K.mem_find _,
mt K.shiftr.mem_iff_find_le.1 by simp only [find_shiftr, not_le, Nat.lt_succ_self]⟩

@[deprecated (since := "2026-06-03")] alias mem_diff_shiftr_find := mem_sdiff_shiftr_find

中文:
定理 mem_sdiff_shiftr_find
  条件: (x : X)
  结论: x in K.shiftr (K.find x + 1) \ K.shiftr (K.find x)
  证明: ⟨K.mem_find _,
mt K.shiftr.mem_iff_find_le.1 by simp only [find_shiftr, not_le, Nat.lt_succ_self]⟩

@[deprecated (since := "2026-06-03")] alias mem_diff_shiftr_find := mem_sdiff_shiftr_find

Depends on / 依赖: K.mem_find, K.shiftr.mem_iff_find_le, Nat.lt_succ_self, find_shiftr, lt_succ_self, mem_find, mem_iff_find_le, not_le, shiftr
-/
theorem mem_sdiff_shiftr_find (x : X) : x in K.shiftr (K.find x + 1) \ K.shiftr (K.find x) :=
  ⟨K.mem_find _,
mt K.shiftr.mem_iff_find_le.1 by simp only [find_shiftr, not_le, Nat.lt_succ_self]⟩

@[deprecated (since := "2026-06-03")] alias mem_diff_shiftr_find := mem_sdiff_shiftr_find

/--
Definition of `choice` / `choice` 的定义

English:
definition choice
  signature: (X : Type*) [TopologicalSpace X] [WeaklyLocallyCompactSpace X]
  body: by
  apply Classical.choice
  let K : Nat -> { s : Set X // IsCompact s } := fun n =>
    Nat.recOn n ⟨∅, isCompact_empty⟩ fun n s =>
      ⟨(exists_compact_superset s.2).choose union compactCovering X n,
        (exists_compact_superset s.2).choose_spec.1.union (isCompact_compactCovering _ _)⟩
  re

中文:
定义 choice
  签名: (X : 类型) [拓扑空间 X] [WeaklyLocallyCompact空间 X]
  定义体: by
  apply Classical.choice
  let K : Nat -> { s : Set X // IsCompact s } := fun n =>
    Nat.recOn n ⟨∅, isCompact_empty⟩ fun n s =>
      ⟨(exists_compact_superset s.2).choose union compactCovering X n,
        (exists_compact_superset s.2).choose_spec.1.union (isCompact_compactCovering _ _)⟩
  re

Depends on / 依赖: Classical, Classical.choice, IsCompact, Nat.recOn, Subset, Subset.trans, choice, choose_spec, compactCovering, exists_compact_superset, iUnion_compactCovering, interior_mono, isCompact_compactCovering, isCompact_empty, subset_union_left, univ_subset_iff
-/
noncomputable def choice (X : Type*) [TopologicalSpace X] [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] : CompactExhaustion X := by
  apply Classical.choice
  let K : Nat -> { s : Set X // IsCompact s } := fun n =>
    Nat.recOn n ⟨∅, isCompact_empty⟩ fun n s =>
      ⟨(exists_compact_superset s.2).choose union compactCovering X n,
        (exists_compact_superset s.2).choose_spec.1.union (isCompact_compactCovering _ _)⟩
  refine ⟨⟨fun n => (K n).1, fun n => (K n).2, fun n => ?_, ?_⟩⟩
  · exact Subset.trans (exists_compact_superset (K n).2).choose_spec.2
      (interior_mono subset_union_left)
  · refine univ_subset_iff.1 (iUnion_compactCovering X ▸ ?_)
    exact iUnion_mono' fun n => ⟨n + 1, subset_union_right⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SigmaCompactSpace
  signature: X] [WeaklyLocallyCompactSpace X] :
  body: ⟨CompactExhaustion.choice X⟩

中文:
实例 [SigmaCompact空间
  签名: X] [WeaklyLocallyCompact空间 X] :
  定义体: ⟨CompactExhaustion.choice X⟩

Depends on / 依赖: CompactExhaustion, CompactExhaustion.choice, choice
-/
noncomputable instance [SigmaCompactSpace X] [WeaklyLocallyCompactSpace X] :
    Inhabited (CompactExhaustion X) :=
  ⟨CompactExhaustion.choice X⟩

end CompactExhaustion
