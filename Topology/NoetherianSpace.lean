/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sets.Closeds

/-!
# Noetherian space

A Noetherian space is a topological space that satisfies any of the following equivalent conditions:
- `WellFounded ((· > ·) : TopologicalSpace.Opens α → TopologicalSpace.Opens α → Prop)`
- `WellFounded ((· < ·) : TopologicalSpace.Closeds α → TopologicalSpace.Closeds α → Prop)`
- `∀ s : Set α, IsCompact s`
- `∀ s : TopologicalSpace.Opens α, IsCompact s`

The first is chosen as the definition, and the equivalence is shown in
`TopologicalSpace.noetherianSpace_TFAE`.

Many examples of Noetherian spaces come from algebraic topology. For example, the underlying space
of a Noetherian scheme (e.g., the spectrum of a Noetherian ring) is Noetherian.

## Main Results

- `TopologicalSpace.NoetherianSpace.set`: Every subspace of a Noetherian space is Noetherian.
- `TopologicalSpace.NoetherianSpace.isCompact`: Every set in a Noetherian space is a compact set.
- `TopologicalSpace.noetherianSpace_TFAE`: Describes the equivalent definitions of Noetherian
  spaces.
- `TopologicalSpace.NoetherianSpace.range`: The image of a Noetherian space under a continuous map
  is Noetherian.
- `TopologicalSpace.NoetherianSpace.iUnion`: The finite union of Noetherian spaces is Noetherian.
- `TopologicalSpace.NoetherianSpace.discrete`: A Noetherian and Hausdorff space is discrete.
- `TopologicalSpace.NoetherianSpace.exists_finset_irreducible`: Every closed subset of a Noetherian
  space is a finite union of irreducible closed subsets.
- `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`: The number of irreducible
  components of a Noetherian space is finite.

-/

public section

open Topology

variable (α β : Type*) [TopologicalSpace α] [TopologicalSpace β]

namespace TopologicalSpace

/--
Definition of `NoetherianSpace` / `NoetherianSpace` 的定义

English:
abbreviation NoetherianSpace
  signature: : Prop
  body: WellFoundedGT (Opens α)

中文:
缩写 NoetherianSpace
  签名: : 命题
  定义体: WellFoundedGT (Opens α)

Depends on / 依赖: WellFoundedGT
-/
abbrev NoetherianSpace : Prop := WellFoundedGT (Opens α)

/--
theorem `noetherianSpace_iff_opens` / 定理 `noetherianSpace_iff_opens`

English:
theorem noetherianSpace_iff_opens
  statement: NoetherianSpace α ↔ forall s : Opens α, IsCompact (s : Set α)
  proof: by
  rw [NoetherianSpace]; rw [CompleteLattice.wellFoundedGT_iff_isSupFiniteCompact]; rw [CompleteLattice.isSupFiniteCompact_iff_all_elements_compact]
  exact forall_congr' Opens.isCompactElement_iff

中文:
定理 noetherianSpace_iff_opens
  结论: NoetherianSpace α ↔ 对任意 s : Opens α, 是紧集 (s : 集合 α)
  证明: by
  rw [NoetherianSpace]; rw [CompleteLattice.wellFoundedGT_iff_isSupFiniteCompact]; rw [CompleteLattice.isSupFiniteCompact_iff_all_elements_compact]
  exact forall_congr' Opens.isCompactElement_iff

Depends on / 依赖: CompleteLattice, CompleteLattice.isSupFiniteCompact_iff_all_elements_compact, CompleteLattice.wellFoundedGT_iff_isSupFiniteCompact, NoetherianSpace, Opens.isCompactElement_iff, forall_congr, isCompactElement_iff, isSupFiniteCompact_iff_all_elements_compact, wellFoundedGT_iff_isSupFiniteCompact
-/
theorem noetherianSpace_iff_opens : NoetherianSpace α ↔ forall s : Opens α, IsCompact (s : Set α) := by
  rw [NoetherianSpace]; rw [CompleteLattice.wellFoundedGT_iff_isSupFiniteCompact]; rw [CompleteLattice.isSupFiniteCompact_iff_all_elements_compact]
  exact forall_congr' Opens.isCompactElement_iff

instance (priority := 100) NoetherianSpace.compactSpace [h : NoetherianSpace α] : CompactSpace α :=
  ⟨(noetherianSpace_iff_opens α).mp h ⊤⟩

variable {α β}

/--
theorem `NoetherianSpace.isCompact` / 定理 `NoetherianSpace.isCompact`

English:
theorem NoetherianSpace.isCompact
  given: [NoetherianSpace α] (s : Set α)
  statement: IsCompact s
  proof: by
  refine isCompact_iff_finite_subcover.2 fun U hUo hs => ?_
  rcases ((noetherianSpace_iff_opens α).mp ‹_› ⟨⋃ i, U i, isOpen_iUnion hUo⟩).elim_finite_subcover U
    hUo Set.Subset.rfl with ⟨t, ht⟩
  exact ⟨t, hs.trans ht⟩

中文:
定理 NoetherianSpace.isCompact
  条件: [NoetherianSpace α] (s : 集合 α)
  结论: 是紧集 s
  证明: by
  refine isCompact_iff_finite_subcover.2 fun U hUo hs => ?_
  rcases ((noetherianSpace_iff_opens α).mp ‹_› ⟨⋃ i, U i, isOpen_iUnion hUo⟩).elim_finite_subcover U
    hUo Set.Subset.rfl with ⟨t, ht⟩
  exact ⟨t, hs.trans ht⟩
-/
protected theorem NoetherianSpace.isCompact [NoetherianSpace α] (s : Set α) : IsCompact s := by
  refine isCompact_iff_finite_subcover.2 fun U hUo hs => ?_
  rcases ((noetherianSpace_iff_opens α).mp ‹_› ⟨⋃ i, U i, isOpen_iUnion hUo⟩).elim_finite_subcover U
    hUo Set.Subset.rfl with ⟨t, ht⟩
  exact ⟨t, hs.trans ht⟩

/--
theorem `_root_.Topology.IsInducing.noetherianSpace` / 定理 `_root_.Topology.IsInducing.noetherianSpace`

English:
theorem _root_.Topology.IsInducing.noetherianSpace
  statement: [NoetherianSpace α] {i : β -> α}
  proof: (noetherianSpace_iff_opens _).2 fun _ => hi.isCompact_iff.2 (NoetherianSpace.isCompact _)

@[stacks 0052 "(1)"]

中文:
定理 _root_.拓扑.是Inducing.noetherianSpace
  结论: [NoetherianSpace α] {i : β -> α}
  证明: (noetherianSpace_iff_opens _).2 fun _ => hi.isCompact_iff.2 (NoetherianSpace.isCompact _)

@[stacks 0052 "(1)"]
-/
protected theorem _root_.Topology.IsInducing.noetherianSpace [NoetherianSpace α] {i : β -> α}
    (hi : IsInducing i) : NoetherianSpace β :=
  (noetherianSpace_iff_opens _).2 fun _ => hi.isCompact_iff.2 (NoetherianSpace.isCompact _)

@[stacks 0052 "(1)"]
/--
Instance `NoetherianSpace.set` / 实例 `NoetherianSpace.set`

English:
instance NoetherianSpace.set
  signature: [NoetherianSpace α] (s : Set α)
  body: IsInducing.subtypeVal.noetherianSpace

中文:
实例 NoetherianSpace.set
  签名: [NoetherianSpace α] (s : 集合 α)
  定义体: IsInducing.subtypeVal.noetherianSpace

Depends on / 依赖: IsInducing, IsInducing.subtypeVal.noetherianSpace, noetherianSpace, subtypeVal
-/
instance NoetherianSpace.set [NoetherianSpace α] (s : Set α) : NoetherianSpace s :=
  IsInducing.subtypeVal.noetherianSpace

variable (α) in
open List in
/--
theorem `noetherianSpace_TFAE` / 定理 `noetherianSpace_TFAE`

English:
theorem noetherianSpace_TFAE
  proof: by
  tfae_have 1 ↔ 2 := by
    simp_rw [isWellFounded_iff]
    exact Opens.compl_bijective.2.wellFounded_iff (@OrderIso.compl (Set α)).lt_iff_lt.symm
  tfae_have 1 ↔ 4 := noetherianSpace_iff_opens α
  tfae_have 1 -> 3 := @NoetherianSpace.isCompact α _
  tfae_have 3 -> 4 := fun h s => h s
  tfae_finish

中文:
定理 noetherianSpace_TFAE
  证明: by
  tfae_have 1 ↔ 2 := by
    simp_rw [isWellFounded_iff]
    exact Opens.compl_bijective.2.wellFounded_iff (@OrderIso.compl (Set α)).lt_iff_lt.symm
  tfae_have 1 ↔ 4 := noetherianSpace_iff_opens α
  tfae_have 1 -> 3 := @NoetherianSpace.isCompact α _
  tfae_have 3 -> 4 := fun h s => h s
  tfae_finish

Depends on / 依赖: NoetherianSpace, NoetherianSpace.isCompact, Opens.compl_bijective, OrderIso, OrderIso.compl, compl_bijective, isCompact, isWellFounded_iff, lt_iff_lt, lt_iff_lt.symm, noetherianSpace_iff_opens, simp_rw, tfae_finish, tfae_have, wellFounded_iff
-/
theorem noetherianSpace_TFAE :
    TFAE [NoetherianSpace α,
      WellFoundedLT (Closeds α),
      forall s : Set α, IsCompact s,
      forall s : Opens α, IsCompact (s : Set α)] := by
  tfae_have 1 ↔ 2 := by
    simp_rw [isWellFounded_iff]
    exact Opens.compl_bijective.2.wellFounded_iff (@OrderIso.compl (Set α)).lt_iff_lt.symm
  tfae_have 1 ↔ 4 := noetherianSpace_iff_opens α
  tfae_have 1 -> 3 := @NoetherianSpace.isCompact α _
  tfae_have 3 -> 4 := fun h s => h s
  tfae_finish

/--
theorem `noetherianSpace_iff_isCompact` / 定理 `noetherianSpace_iff_isCompact`

English:
theorem noetherianSpace_iff_isCompact
  statement: NoetherianSpace α ↔ forall s : Set α, IsCompact s
  proof: (noetherianSpace_TFAE α).out 0 2

中文:
定理 noetherianSpace_iff_isCompact
  结论: NoetherianSpace α ↔ 对任意 s : 集合 α, 是紧集 s
  证明: (noetherianSpace_TFAE α).out 0 2

Depends on / 依赖: noetherianSpace_TFAE
-/
theorem noetherianSpace_iff_isCompact : NoetherianSpace α ↔ forall s : Set α, IsCompact s :=
  (noetherianSpace_TFAE α).out 0 2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoetherianSpace
  signature: α] : WellFoundedLT (Closeds α)
  body: Iff.mp ((noetherianSpace_TFAE α).out 0 1) ‹_›

中文:
实例 [NoetherianSpace
  签名: α] : WellFoundedLT (Closeds α)
  定义体: Iff.mp ((noetherianSpace_TFAE α).out 0 1) ‹_›

Depends on / 依赖: Iff.mp, noetherianSpace_TFAE
-/
instance [NoetherianSpace α] : WellFoundedLT (Closeds α) :=
  Iff.mp ((noetherianSpace_TFAE α).out 0 1) ‹_›

instance {α} : NoetherianSpace (CofiniteTopology α) := by
  simp only [noetherianSpace_iff_isCompact, isCompact_iff_ultrafilter_le_nhds,
    CofiniteTopology.nhds_eq, Ultrafilter.le_sup_iff, Filter.le_principal_iff]
  intro s f hs
  rcases f.le_cofinite_or_eq_pure with (hf | ⟨a, rfl⟩)
  · rcases Filter.nonempty_of_mem hs with ⟨a, ha⟩
    exact ⟨a, ha, Or.inr hf⟩
  · exact ⟨a, hs, Or.inl le_rfl⟩

/--
theorem `noetherianSpace_of_surjective` / 定理 `noetherianSpace_of_surjective`

English:
theorem noetherianSpace_of_surjective
  statement: [NoetherianSpace α] (f : α -> β) (hf : Continuous f)
  proof: noetherianSpace_iff_isCompact.2 (Set.image_surjective.mpr hf').forall.2 fun s =>
    (NoetherianSpace.isCompact s).image hf

中文:
定理 noetherianSpace_of_surjective
  结论: [NoetherianSpace α] (f : α -> β) (hf : 连续 f)
  证明: noetherianSpace_iff_isCompact.2 (Set.image_surjective.mpr hf').forall.2 fun s =>
    (NoetherianSpace.isCompact s).image hf

Depends on / 依赖: NoetherianSpace, NoetherianSpace.isCompact, Set.image_surjective.mpr, image_surjective, isCompact, noetherianSpace_iff_isCompact
-/
theorem noetherianSpace_of_surjective [NoetherianSpace α] (f : α -> β) (hf : Continuous f)
    (hf' : Function.Surjective f) : NoetherianSpace β :=
noetherianSpace_iff_isCompact.2 (Set.image_surjective.mpr hf').forall.2 fun s =>
    (NoetherianSpace.isCompact s).image hf

/--
theorem `noetherianSpace_iff_of_homeomorph` / 定理 `noetherianSpace_iff_of_homeomorph`

English:
theorem noetherianSpace_iff_of_homeomorph
  given: (f : α ≃ₜ β)
  statement: NoetherianSpace α ↔ NoetherianSpace β
  proof: ⟨fun _ => noetherianSpace_of_surjective f f.continuous f.surjective,
    fun _ => noetherianSpace_of_surjective f.symm f.symm.continuous f.symm.surjective⟩

中文:
定理 noetherianSpace_iff_of_homeomorph
  条件: (f : α ≃ₜ β)
  结论: NoetherianSpace α ↔ NoetherianSpace β
  证明: ⟨fun _ => noetherianSpace_of_surjective f f.continuous f.surjective,
    fun _ => noetherianSpace_of_surjective f.symm f.symm.continuous f.symm.surjective⟩

Depends on / 依赖: continuous, f.continuous, f.surjective, f.symm, f.symm.continuous, f.symm.surjective, noetherianSpace_of_surjective, surjective
-/
theorem noetherianSpace_iff_of_homeomorph (f : α ≃ₜ β) : NoetherianSpace α ↔ NoetherianSpace β :=
  ⟨fun _ => noetherianSpace_of_surjective f f.continuous f.surjective,
    fun _ => noetherianSpace_of_surjective f.symm f.symm.continuous f.symm.surjective⟩

/--
theorem `NoetherianSpace.range` / 定理 `NoetherianSpace.range`

English:
theorem NoetherianSpace.range
  given: [NoetherianSpace α] (f : α -> β) (hf : Continuous f)
  proof: noetherianSpace_of_surjective (Set.rangeFactorization f) (hf.subtype_mk _)
    Set.rangeFactorization_surjective

中文:
定理 NoetherianSpace.range
  条件: [NoetherianSpace α] (f : α -> β) (hf : 连续 f)
  证明: noetherianSpace_of_surjective (Set.rangeFactorization f) (hf.subtype_mk _)
    Set.rangeFactorization_surjective

Depends on / 依赖: Set.rangeFactorization, Set.rangeFactorization_surjective, hf.subtype_mk, noetherianSpace_of_surjective, rangeFactorization, rangeFactorization_surjective, subtype_mk
-/
theorem NoetherianSpace.range [NoetherianSpace α] (f : α -> β) (hf : Continuous f) :
    NoetherianSpace (Set.range f) :=
  noetherianSpace_of_surjective (Set.rangeFactorization f) (hf.subtype_mk _)
    Set.rangeFactorization_surjective

/--
theorem `noetherianSpace_set_iff` / 定理 `noetherianSpace_set_iff`

English:
theorem noetherianSpace_set_iff
  given: (s : Set α)
  proof: by
  simp only [noetherianSpace_iff_isCompact, IsEmbedding.subtypeVal.isCompact_iff,
    Subtype.forall_set_subtype]

@[simp]

中文:
定理 noetherianSpace_set_iff
  条件: (s : 集合 α)
  证明: by
  simp only [noetherianSpace_iff_isCompact, IsEmbedding.subtypeVal.isCompact_iff,
    Subtype.forall_set_subtype]

@[simp]

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.isCompact_iff, Subtype, Subtype.forall_set_subtype, forall_set_subtype, isCompact_iff, noetherianSpace_iff_isCompact, subtypeVal
-/
theorem noetherianSpace_set_iff (s : Set α) :
    NoetherianSpace s ↔ forall t, t subseteq s -> IsCompact t := by
  simp only [noetherianSpace_iff_isCompact, IsEmbedding.subtypeVal.isCompact_iff,
    Subtype.forall_set_subtype]

@[simp]
/--
theorem `noetherian_univ_iff` / 定理 `noetherian_univ_iff`

English:
theorem noetherian_univ_iff
  statement: NoetherianSpace (Set.univ : Set α) ↔ NoetherianSpace α
  proof: noetherianSpace_iff_of_homeomorph (Homeomorph.Set.univ α)

中文:
定理 noetherian_univ_iff
  结论: NoetherianSpace (集合.univ : 集合 α) ↔ NoetherianSpace α
  证明: noetherianSpace_iff_of_homeomorph (Homeomorph.Set.univ α)

Depends on / 依赖: Homeomorph, Homeomorph.Set.univ, noetherianSpace_iff_of_homeomorph
-/
theorem noetherian_univ_iff : NoetherianSpace (Set.univ : Set α) ↔ NoetherianSpace α :=
  noetherianSpace_iff_of_homeomorph (Homeomorph.Set.univ α)

/--
theorem `NoetherianSpace.iUnion` / 定理 `NoetherianSpace.iUnion`

English:
theorem NoetherianSpace.iUnion
  statement: {ι : Type*} (f : ι -> Set α) [Finite ι]
  proof: by
  simp_rw [noetherianSpace_set_iff] at hf ⊢
  intro t ht
  rw [← Set.inter_eq_left.mpr ht]; rw [Set.inter_iUnion]
  exact isCompact_iUnion fun i => hf i _ Set.inter_subset_right

中文:
定理 NoetherianSpace.iUnion
  结论: {ι : 类型} (f : ι -> 集合 α) [有限 ι]
  证明: by
  simp_rw [noetherianSpace_set_iff] at hf ⊢
  intro t ht
  rw [← Set.inter_eq_left.mpr ht]; rw [Set.inter_iUnion]
  exact isCompact_iUnion fun i => hf i _ Set.inter_subset_right

Depends on / 依赖: Set.inter_eq_left.mpr, Set.inter_iUnion, Set.inter_subset_right, inter_eq_left, inter_iUnion, inter_subset_right, isCompact_iUnion, noetherianSpace_set_iff, simp_rw
-/
theorem NoetherianSpace.iUnion {ι : Type*} (f : ι -> Set α) [Finite ι]
    [hf : forall i, NoetherianSpace (f i)] : NoetherianSpace (⋃ i, f i) := by
  simp_rw [noetherianSpace_set_iff] at hf ⊢
  intro t ht
  rw [← Set.inter_eq_left.mpr ht]; rw [Set.inter_iUnion]
  exact isCompact_iUnion fun i => hf i _ Set.inter_subset_right

-- This is not an instance since it makes a loop with `t2_space_discrete`.
/--
theorem `NoetherianSpace.discrete` / 定理 `NoetherianSpace.discrete`

English:
theorem NoetherianSpace.discrete
  given: [NoetherianSpace α] [T2Space α]
  statement: DiscreteTopology α
  proof: ⟨eq_bot_iff.mpr fun _ _ => isClosed_compl_iff.mp (NoetherianSpace.isCompact _).isClosed⟩

中文:
定理 NoetherianSpace.discrete
  条件: [NoetherianSpace α] [T2空间 α]
  结论: 离散拓扑 α
  证明: ⟨eq_bot_iff.mpr fun _ _ => isClosed_compl_iff.mp (NoetherianSpace.isCompact _).isClosed⟩

Depends on / 依赖: NoetherianSpace, NoetherianSpace.isCompact, eq_bot_iff, eq_bot_iff.mpr, isClosed, isClosed_compl_iff, isClosed_compl_iff.mp, isCompact
-/
theorem NoetherianSpace.discrete [NoetherianSpace α] [T2Space α] : DiscreteTopology α :=
  ⟨eq_bot_iff.mpr fun _ _ => isClosed_compl_iff.mp (NoetherianSpace.isCompact _).isClosed⟩

attribute [local instance] NoetherianSpace.discrete

/--
theorem `NoetherianSpace.finite` / 定理 `NoetherianSpace.finite`

English:
theorem NoetherianSpace.finite
  given: [NoetherianSpace α] [T2Space α]
  statement: Finite α
  proof: Finite.of_finite_univ (NoetherianSpace.isCompact Set.univ).finite_of_discrete

中文:
定理 NoetherianSpace.finite
  条件: [NoetherianSpace α] [T2空间 α]
  结论: 有限 α
  证明: Finite.of_finite_univ (NoetherianSpace.isCompact Set.univ).finite_of_discrete

Depends on / 依赖: Finite, Finite.of_finite_univ, NoetherianSpace, NoetherianSpace.isCompact, Set.univ, finite_of_discrete, isCompact, of_finite_univ
-/
theorem NoetherianSpace.finite [NoetherianSpace α] [T2Space α] : Finite α :=
  Finite.of_finite_univ (NoetherianSpace.isCompact Set.univ).finite_of_discrete

instance (priority := 100) Finite.to_noetherianSpace [Finite α] : NoetherianSpace α :=
  ⟨Finite.wellFounded_of_trans_of_irrefl _⟩

instance (priority := 100) [IndiscreteTopology α] : NoetherianSpace α :=
  noetherianSpace_of_surjective CofiniteTopology.of.symm continuous_of_indiscreteTopology
    CofiniteTopology.of.symm.surjective

/--
theorem `NoetherianSpace.exists_finite_set_closeds_irreducible` / 定理 `NoetherianSpace.exists_finite_set_closeds_irreducible`

English:
theorem NoetherianSpace.exists_finite_set_closeds_irreducible
  given: [NoetherianSpace α] (s : Closeds α)
  proof: by
  apply wellFounded_lt.induction s; clear s
  intro s H
  rcases eq_or_ne s ⊥ with rfl | h₀
  · use ∅; simp
  · by_cases h₁ : IsPreirreducible (s : Set α)
    · replace h₁ : IsIrreducible (s : Set α) := ⟨Closeds.coe_nonempty.2 h₀, h₁⟩
      use {s}; simp [h₁]
    · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at h₁
      obtain ⟨z₁, z₂, hz₁, hz₂, h, hz₁', hz₂'⟩ := h₁
      lift z₁ to Closeds α using hz₁
      lift z₂ to Closeds α using hz₂
      rcases H (s ⊓ z₁) (inf_lt_left.2 hz₁') with ⟨S₁, hSf₁, hS₁, h₁⟩
      rcases H (s ⊓ z₂) (inf_lt_left.2 hz₂') with ⟨S₂, hSf₂, hS₂, h₂⟩
      refine ⟨S₁ union S₂, hSf₁.union hSf₂, Set.union_subset_iff.2 ⟨hS₁, hS₂⟩, ?_⟩
      rwa [sSup_union, ← h₁, ← h₂, ← inf_sup_left, left_eq_inf]

中文:
定理 NoetherianSpace.存在_finite_set_closeds_irreducible
  条件: [NoetherianSpace α] (s : Closeds α)
  证明: by
  apply wellFounded_lt.induction s; clear s
  intro s H
  rcases eq_or_ne s ⊥ with rfl | h₀
  · use ∅; simp
  · by_cases h₁ : IsPreirreducible (s : Set α)
    · replace h₁ : IsIrreducible (s : Set α) := ⟨Closeds.coe_nonempty.2 h₀, h₁⟩
      use {s}; simp [h₁]
    · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at h₁
      obtain ⟨z₁, z₂, hz₁, hz₂, h, hz₁', hz₂'⟩ := h₁
      lift z₁ to Closeds α using hz₁
      lift z₂ to Closeds α using hz₂
      rcases H (s ⊓ z₁) (inf_lt_left.2 hz₁') with ⟨S₁, hSf₁, hS₁, h₁⟩
      rcases H (s ⊓ z₂) (inf_lt_left.2 hz₂') with ⟨S₂, hSf₂, hS₂, h₂⟩
      refine ⟨S₁ union S₂, hSf₁.union hSf₂, Set.union_subset_iff.2 ⟨hS₁, hS₂⟩, ?_⟩
      rwa [sSup_union, ← h₁, ← h₂, ← inf_sup_left, left_eq_inf]

Depends on / 依赖: Closeds, Closeds.coe_nonempty, IsIrreducible, IsPreirreducible, coe_nonempty, eq_or_ne, inf_lt_left, isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or, replace, wellFounded_lt, wellFounded_lt.induction
-/
theorem NoetherianSpace.exists_finite_set_closeds_irreducible [NoetherianSpace α] (s : Closeds α) :
    exists S : Set (Closeds α), S.Finite ∧ (forall t in S, IsIrreducible (t : Set α)) ∧ s = sSup S := by
  apply wellFounded_lt.induction s; clear s
  intro s H
  rcases eq_or_ne s ⊥ with rfl | h₀
  · use ∅; simp
  · by_cases h₁ : IsPreirreducible (s : Set α)
    · replace h₁ : IsIrreducible (s : Set α) := ⟨Closeds.coe_nonempty.2 h₀, h₁⟩
      use {s}; simp [h₁]
    · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at h₁
      obtain ⟨z₁, z₂, hz₁, hz₂, h, hz₁', hz₂'⟩ := h₁
      lift z₁ to Closeds α using hz₁
      lift z₂ to Closeds α using hz₂
      rcases H (s ⊓ z₁) (inf_lt_left.2 hz₁') with ⟨S₁, hSf₁, hS₁, h₁⟩
      rcases H (s ⊓ z₂) (inf_lt_left.2 hz₂') with ⟨S₂, hSf₂, hS₂, h₂⟩
      refine ⟨S₁ union S₂, hSf₁.union hSf₂, Set.union_subset_iff.2 ⟨hS₁, hS₂⟩, ?_⟩
      rwa [sSup_union, ← h₁, ← h₂, ← inf_sup_left, left_eq_inf]

/--
theorem `NoetherianSpace.exists_finite_set_isClosed_irreducible` / 定理 `NoetherianSpace.exists_finite_set_isClosed_irreducible`

English:
theorem NoetherianSpace.exists_finite_set_isClosed_irreducible
  statement: [NoetherianSpace α]
  proof: by
  lift s to Closeds α using hs
  rcases NoetherianSpace.exists_finite_set_closeds_irreducible s with ⟨S, hSf, hS, rfl⟩
  refine ⟨(↑) '' S, hSf.image _, Set.forall_mem_image.2 fun S _ => S.2, Set.forall_mem_image.2 hS,
    ?_⟩
  lift S to Finset (Closeds α) using hSf
  simp [← Finset.sup_id_eq_sSup, Closeds.coe_finset_sup]

中文:
定理 NoetherianSpace.存在_finite_set_isClosed_irreducible
  结论: [NoetherianSpace α]
  证明: by
  lift s to Closeds α using hs
  rcases NoetherianSpace.exists_finite_set_closeds_irreducible s with ⟨S, hSf, hS, rfl⟩
  refine ⟨(↑) '' S, hSf.image _, Set.forall_mem_image.2 fun S _ => S.2, Set.forall_mem_image.2 hS,
    ?_⟩
  lift S to Finset (Closeds α) using hSf
  simp [← Finset.sup_id_eq_sSup, Closeds.coe_finset_sup]

Depends on / 依赖: Closeds, Closeds.coe_finset_sup, Finset, Finset.sup_id_eq_sSup, NoetherianSpace, NoetherianSpace.exists_finite_set_closeds_irreducible, Set.forall_mem_image, coe_finset_sup, exists_finite_set_closeds_irreducible, forall_mem_image, hSf.image, sup_id_eq_sSup
-/
theorem NoetherianSpace.exists_finite_set_isClosed_irreducible [NoetherianSpace α]
    {s : Set α} (hs : IsClosed s) : exists S : Set (Set α), S.Finite ∧
      (forall t in S, IsClosed t) ∧ (forall t in S, IsIrreducible t) ∧ s = ⋃₀ S := by
  lift s to Closeds α using hs
  rcases NoetherianSpace.exists_finite_set_closeds_irreducible s with ⟨S, hSf, hS, rfl⟩
  refine ⟨(↑) '' S, hSf.image _, Set.forall_mem_image.2 fun S _ => S.2, Set.forall_mem_image.2 hS,
    ?_⟩
  lift S to Finset (Closeds α) using hSf
  simp [← Finset.sup_id_eq_sSup, Closeds.coe_finset_sup]

/--
theorem `NoetherianSpace.exists_finset_irreducible` / 定理 `NoetherianSpace.exists_finset_irreducible`

English:
theorem NoetherianSpace.exists_finset_irreducible
  given: [NoetherianSpace α] (s : Closeds α)
  proof: by
  simpa [Set.exists_finite_iff_finset, Finset.sup_id_eq_sSup]
    using NoetherianSpace.exists_finite_set_closeds_irreducible s

@[stacks 0052 "(2)"]

中文:
定理 NoetherianSpace.存在_finset_irreducible
  条件: [NoetherianSpace α] (s : Closeds α)
  证明: by
  simpa [Set.exists_finite_iff_finset, Finset.sup_id_eq_sSup]
    using NoetherianSpace.exists_finite_set_closeds_irreducible s

@[stacks 0052 "(2)"]

Depends on / 依赖: Finset, Finset.sup_id_eq_sSup, NoetherianSpace, NoetherianSpace.exists_finite_set_closeds_irreducible, Set.exists_finite_iff_finset, exists_finite_iff_finset, exists_finite_set_closeds_irreducible, sup_id_eq_sSup
-/
theorem NoetherianSpace.exists_finset_irreducible [NoetherianSpace α] (s : Closeds α) :
    exists S : Finset (Closeds α), (forall k : S, IsIrreducible (k : Set α)) ∧ s = S.sup id := by
  simpa [Set.exists_finite_iff_finset, Finset.sup_id_eq_sSup]
    using NoetherianSpace.exists_finite_set_closeds_irreducible s

@[stacks 0052 "(2)"]
/--
theorem `NoetherianSpace.finite_irreducibleComponents` / 定理 `NoetherianSpace.finite_irreducibleComponents`

English:
theorem NoetherianSpace.finite_irreducibleComponents
  given: [NoetherianSpace α]
  proof: by
  obtain ⟨S : Set (Set α), hSf, hSc, hSi, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible isClosed_univ (α := α)
  refine hSf.subset fun s hs => ?_
  lift S to Finset (Set α) using hSf
  rcases isIrreducible_iff_sUnion_isClosed.1 hs.1 S hSc (hSU ▸ Set.subset_univ _) with ⟨t, htS, ht⟩
  rwa [ht.antisymm (hs.2 (hSi _ htS) ht)]

@[stacks 0052 "(3)"]

中文:
定理 NoetherianSpace.finite_irreducibleComponents
  条件: [NoetherianSpace α]
  证明: by
  obtain ⟨S : Set (Set α), hSf, hSc, hSi, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible isClosed_univ (α := α)
  refine hSf.subset fun s hs => ?_
  lift S to Finset (Set α) using hSf
  rcases isIrreducible_iff_sUnion_isClosed.1 hs.1 S hSc (hSU ▸ Set.subset_univ _) with ⟨t, htS, ht⟩
  rwa [ht.antisymm (hs.2 (hSi _ htS) ht)]

@[stacks 0052 "(3)"]

Depends on / 依赖: Finset, NoetherianSpace, NoetherianSpace.exists_finite_set_isClosed_irreducible, Set.subset_univ, antisymm, exists_finite_set_isClosed_irreducible, hSf.subset, ht.antisymm, isClosed_univ, isIrreducible_iff_sUnion_isClosed, subset, subset_univ
-/
theorem NoetherianSpace.finite_irreducibleComponents [NoetherianSpace α] :
    (irreducibleComponents α).Finite := by
  obtain ⟨S : Set (Set α), hSf, hSc, hSi, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible isClosed_univ (α := α)
  refine hSf.subset fun s hs => ?_
  lift S to Finset (Set α) using hSf
  rcases isIrreducible_iff_sUnion_isClosed.1 hs.1 S hSc (hSU ▸ Set.subset_univ _) with ⟨t, htS, ht⟩
  rwa [ht.antisymm (hs.2 (hSi _ htS) ht)]

@[stacks 0052 "(3)"]
/--
theorem `NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent` / 定理 `NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent`

English:
theorem NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
  statement: [NoetherianSpace α]
  proof: by
  have hα : (irreducibleComponents α).Finite := finite_irreducibleComponents
  have hZ := closure_sUnion_irreducibleComponents_sdiff_singleton hα Z H
  refine ⟨(⋃₀ (irreducibleComponents α \ {Z}))ᶜ, ?_, ?_, subset_closure.trans hZ.le⟩
  · rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hα.sdiff.isClosed_biUnion fun W hW => isClosed_of_mem_irreducibleComponents W hW.1
  · contrapose! hZ
    rw [hZ]; rw [closure_empty]; rw [← Set.nonempty_iff_empty_ne]
    exact H.1.nonempty

中文:
定理 NoetherianSpace.存在_isOpen_nonempty_subset_irreducibleComponent
  结论: [NoetherianSpace α]
  证明: by
  have hα : (irreducibleComponents α).Finite := finite_irreducibleComponents
  have hZ := closure_sUnion_irreducibleComponents_sdiff_singleton hα Z H
  refine ⟨(⋃₀ (irreducibleComponents α \ {Z}))ᶜ, ?_, ?_, subset_closure.trans hZ.le⟩
  · rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hα.sdiff.isClosed_biUnion fun W hW => isClosed_of_mem_irreducibleComponents W hW.1
  · contrapose! hZ
    rw [hZ]; rw [closure_empty]; rw [← Set.nonempty_iff_empty_ne]
    exact H.1.nonempty

Depends on / 依赖: Finite, Set.nonempty_iff_empty_ne, Set.sUnion_eq_biUnion, closure_empty, closure_sUnion_irreducibleComponents_sdiff_singleton, contrapose, finite_irreducibleComponents, hZ.le, irreducibleComponents, isClosed_biUnion, isClosed_of_mem_irreducibleComponents, isOpen_compl_iff, nonempty, nonempty_iff_empty_ne, sUnion_eq_biUnion, sdiff.isClosed_biUnion, subset_closure, subset_closure.trans
-/
theorem NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent [NoetherianSpace α]
    (Z : Set α) (H : Z in irreducibleComponents α) :
    exists o : Set α, IsOpen o ∧ o.Nonempty ∧ o subseteq Z := by
  have hα : (irreducibleComponents α).Finite := finite_irreducibleComponents
  have hZ := closure_sUnion_irreducibleComponents_sdiff_singleton hα Z H
  refine ⟨(⋃₀ (irreducibleComponents α \ {Z}))ᶜ, ?_, ?_, subset_closure.trans hZ.le⟩
  · rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hα.sdiff.isClosed_biUnion fun W hW => isClosed_of_mem_irreducibleComponents W hW.1
  · contrapose! hZ
    rw [hZ]; rw [closure_empty]; rw [← Set.nonempty_iff_empty_ne]
    exact H.1.nonempty

/--
lemma `NoetherianSpace.of_subset` / 引理 `NoetherianSpace.of_subset`

English:
lemma NoetherianSpace.of_subset
  statement: {W V : Set α} [NoetherianSpace W]
  proof: Topology.IsInducing.noetherianSpace (Topology.IsEmbedding.inclusion h).isInducing

中文:
引理 NoetherianSpace.of_subset
  结论: {W V : 集合 α} [NoetherianSpace W]
  证明: Topology.IsInducing.noetherianSpace (Topology.IsEmbedding.inclusion h).isInducing

Depends on / 依赖: IsEmbedding, IsInducing, Topology, Topology.IsEmbedding.inclusion, Topology.IsInducing.noetherianSpace, inclusion, isInducing, noetherianSpace
-/
lemma NoetherianSpace.of_subset {W V : Set α} [NoetherianSpace W]
    (h : V subseteq W) : NoetherianSpace V :=
  Topology.IsInducing.noetherianSpace (Topology.IsEmbedding.inclusion h).isInducing

/--
lemma `NoetherianSpace.inter_of_left` / 引理 `NoetherianSpace.inter_of_left`

English:
lemma NoetherianSpace.inter_of_left
  given: (W V : Set α) [NoetherianSpace W]
  proof: .of_subset Set.inter_subset_left

中文:
引理 NoetherianSpace.inter_of_left
  条件: (W V : 集合 α) [NoetherianSpace W]
  证明: .of_subset Set.inter_subset_left

Depends on / 依赖: Set.inter_subset_left, inter_subset_left, of_subset
-/
lemma NoetherianSpace.inter_of_left (W V : Set α) [NoetherianSpace W] :
    NoetherianSpace (W inter V : Set α) := .of_subset Set.inter_subset_left

/--
lemma `NoetherianSpace.inter_of_right` / 引理 `NoetherianSpace.inter_of_right`

English:
lemma NoetherianSpace.inter_of_right
  given: (W V : Set α) [NoetherianSpace V]
  proof: .of_subset Set.inter_subset_right

中文:
引理 NoetherianSpace.inter_of_right
  条件: (W V : 集合 α) [NoetherianSpace V]
  证明: .of_subset Set.inter_subset_right

Depends on / 依赖: Set.inter_subset_right, inter_subset_right, of_subset
-/
lemma NoetherianSpace.inter_of_right (W V : Set α) [NoetherianSpace V] :
    NoetherianSpace (W inter V : Set α) := .of_subset Set.inter_subset_right

end TopologicalSpace
