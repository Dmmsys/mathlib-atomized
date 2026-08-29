/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Order.Filter.Bases.Basic
public import Mathlib.Order.Filter.Finite

/-!
# Finiteness results on filter bases

A filter basis `B : FilterBasis α` on a type `α` is a nonempty collection of sets of `α`
such that the intersection of two elements of this collection contains some element of
the collection.
-/

@[expose] public section

open Set Filter

variable {α β γ : Type*} {ι ι' : Sort*}

namespace Filter

section SameType

variable {l l' : Filter α} {p : ι -> Prop} {s : ι -> Set α} {t : Set α} {i : ι} {p' : ι' -> Prop}
  {s' : ι' -> Set α} {i' : ι'}

/--
theorem `hasBasis_generate` / 定理 `hasBasis_generate`

English:
theorem hasBasis_generate
  given: (s : Set (Set α))
  proof: ⟨fun U => by simp only [mem_generate_iff, and_assoc, and_left_comm]⟩

中文:
定理 hasBasis_generate
  条件: (s : Set (Set α))
  证明: ⟨fun U => by simp only [mem_generate_iff, and_assoc, and_left_comm]⟩

Depends on / 依赖: and_assoc, and_left_comm, mem_generate_iff
-/
theorem hasBasis_generate (s : Set (Set α)) :
    (generate s).HasBasis (fun t => Set.Finite t ∧ t subseteq s) fun t => ⋂₀ t :=
  ⟨fun U => by simp only [mem_generate_iff, and_assoc, and_left_comm]⟩

/--
Definition of `FilterBasis.ofSets` / `FilterBasis.ofSets` 的定义

English:
definition FilterBasis.ofSets
  signature: (s : Set (Set α))
  body: sInter '' { t | Set.Finite t ∧ t subseteq s }
  nonempty := ⟨univ, ∅, ⟨⟨finite_empty, empty_subset s⟩, sInter_empty⟩⟩
  inter_sets := by
    rintro _ _ ⟨a, ⟨fina, suba⟩, rfl⟩ ⟨b, ⟨finb, subb⟩, rfl⟩
    exact ⟨⋂₀ (a union b), mem_image_of_mem _ ⟨fina.union finb, union_subset suba subb⟩,
        (sInt

中文:
定义 FilterBasis.ofSets
  签名: (s : Set (Set α))
  定义体: sInter '' { t | Set.Finite t ∧ t subseteq s }
  nonempty := ⟨univ, ∅, ⟨⟨finite_empty, empty_subset s⟩, sInter_empty⟩⟩
  inter_sets := by
    rintro _ _ ⟨a, ⟨fina, suba⟩, rfl⟩ ⟨b, ⟨finb, subb⟩, rfl⟩
    exact ⟨⋂₀ (a union b), mem_image_of_mem _ ⟨fina.union finb, union_subset suba subb⟩,
        (sInt

Depends on / 依赖: Finite, Set.Finite, sInter, subseteq
-/
def FilterBasis.ofSets (s : Set (Set α)) : FilterBasis α where
  sets := sInter '' { t | Set.Finite t ∧ t subseteq s }
  nonempty := ⟨univ, ∅, ⟨⟨finite_empty, empty_subset s⟩, sInter_empty⟩⟩
  inter_sets := by
    rintro _ _ ⟨a, ⟨fina, suba⟩, rfl⟩ ⟨b, ⟨finb, subb⟩, rfl⟩
    exact ⟨⋂₀ (a union b), mem_image_of_mem _ ⟨fina.union finb, union_subset suba subb⟩,
        (sInter_union _ _).subset⟩

/--
lemma `FilterBasis.ofSets_sets` / 引理 `FilterBasis.ofSets_sets`

English:
lemma FilterBasis.ofSets_sets
  given: (s : Set (Set α))
  proof: rfl

中文:
引理 FilterBasis.ofSets_sets
  条件: (s : Set (Set α))
  证明: rfl
-/
lemma FilterBasis.ofSets_sets (s : Set (Set α)) :
    (FilterBasis.ofSets s).sets = sInter '' { t | Set.Finite t ∧ t subseteq s } :=
  rfl

/--
theorem `generate_eq_generate_inter` / 定理 `generate_eq_generate_inter`

English:
theorem generate_eq_generate_inter
  given: (s : Set (Set α))
  proof: by
  rw [← FilterBasis.ofSets_sets]; rw [FilterBasis.generate]; rw [← (hasBasis_generate s).filter_eq]; rfl

中文:
定理 generate_eq_generate_inter
  条件: (s : Set (Set α))
  证明: by
  rw [← FilterBasis.ofSets_sets]; rw [FilterBasis.generate]; rw [← (hasBasis_generate s).filter_eq]; rfl

Depends on / 依赖: FilterBasis, FilterBasis.generate, FilterBasis.ofSets_sets, filter_eq, generate, hasBasis_generate, ofSets_sets
-/
theorem generate_eq_generate_inter (s : Set (Set α)) :
    generate s = generate (sInter '' { t | Set.Finite t ∧ t subseteq s }) := by
  rw [← FilterBasis.ofSets_sets]; rw [FilterBasis.generate]; rw [← (hasBasis_generate s).filter_eq]; rfl

/--
theorem `ofSets_filter_eq_generate` / 定理 `ofSets_filter_eq_generate`

English:
theorem ofSets_filter_eq_generate
  given: (s : Set (Set α))
  proof: by
  rw [← (FilterBasis.ofSets s).generate]; rw [FilterBasis.ofSets_sets]; rw [← generate_eq_generate_inter]

中文:
定理 ofSets_filter_eq_generate
  条件: (s : Set (Set α))
  证明: by
  rw [← (FilterBasis.ofSets s).generate]; rw [FilterBasis.ofSets_sets]; rw [← generate_eq_generate_inter]

Depends on / 依赖: FilterBasis, FilterBasis.ofSets, FilterBasis.ofSets_sets, generate, generate_eq_generate_inter, ofSets, ofSets_sets
-/
theorem ofSets_filter_eq_generate (s : Set (Set α)) :
    (FilterBasis.ofSets s).filter = generate s := by
  rw [← (FilterBasis.ofSets s).generate]; rw [FilterBasis.ofSets_sets]; rw [← generate_eq_generate_inter]

/--
theorem `generate_neBot_iff` / 定理 `generate_neBot_iff`

English:
theorem generate_neBot_iff
  given: {s : Set (Set α)}
  proof: (hasBasis_generate s).neBot_iff.trans by simp only [← and_imp, and_comm]

中文:
定理 generate_neBot_iff
  条件: {s : Set (Set α)}
  证明: (hasBasis_generate s).neBot_iff.trans by simp only [← and_imp, and_comm]

Depends on / 依赖: and_comm, and_imp, hasBasis_generate, neBot_iff, neBot_iff.trans
-/
theorem generate_neBot_iff {s : Set (Set α)} :
    NeBot (generate s) ↔ forall t, t subseteq s -> t.Finite -> (⋂₀ t).Nonempty :=
(hasBasis_generate s).neBot_iff.trans by simp only [← and_imp, and_comm]

/--
theorem `HasBasis.iInf'` / 定理 `HasBasis.iInf'`

English:
theorem HasBasis.iInf'
  statement: {ι : Type*} {ι' : ι -> Type*} {l : ι -> Filter α}
  proof: ⟨by
    intro t
    constructor
    · simp only [mem_iInf', (hl _).mem_iff]
      rintro ⟨I, hI, V, hV, -, rfl, -⟩
      choose u hu using hV
      exact ⟨⟨I, u⟩, ⟨hI, fun i _ => (hu i).1⟩, iInter₂_mono fun i _ => (hu i).2⟩
    · rintro ⟨⟨I, f⟩, ⟨hI₁, hI₂⟩, hsub⟩
      grw [← hsub]
exact (biInter_me

中文:
定理 HasBasis.iInf'
  结论: {ι : 类型} {ι' : ι -> 类型} {l : ι -> Filter α}
  证明: ⟨by
    intro t
    constructor
    · simp only [mem_iInf', (hl _).mem_iff]
      rintro ⟨I, hI, V, hV, -, rfl, -⟩
      choose u hu using hV
      exact ⟨⟨I, u⟩, ⟨hI, fun i _ => (hu i).1⟩, iInter₂_mono fun i _ => (hu i).2⟩
    · rintro ⟨⟨I, f⟩, ⟨hI₁, hI₂⟩, hsub⟩
      grw [← hsub]
exact (biInter_me
-/
protected theorem HasBasis.iInf' {ι : Type*} {ι' : ι -> Type*} {l : ι -> Filter α}
    {p : forall i, ι' i -> Prop} {s : forall i, ι' i -> Set α} (hl : forall i, (l i).HasBasis (p i) (s i)) :
    (⨅ i, l i).HasBasis (fun If : Set ι × forall i, ι' i => If.1.Finite ∧ forall i in If.1, p i (If.2 i))
      fun If : Set ι × forall i, ι' i => ⋂ i in If.1, s i (If.2 i) :=
  ⟨by
    intro t
    constructor
    · simp only [mem_iInf', (hl _).mem_iff]
      rintro ⟨I, hI, V, hV, -, rfl, -⟩
      choose u hu using hV
      exact ⟨⟨I, u⟩, ⟨hI, fun i _ => (hu i).1⟩, iInter₂_mono fun i _ => (hu i).2⟩
    · rintro ⟨⟨I, f⟩, ⟨hI₁, hI₂⟩, hsub⟩
      grw [← hsub]
exact (biInter_mem hI₁).mpr fun i hi => mem_iInf_of_mem i (hl i).mem_of_mem hI₂ _ hi⟩

/--
theorem `HasBasis.iInf` / 定理 `HasBasis.iInf`

English:
theorem HasBasis.iInf
  statement: {ι : Type*} {ι' : ι -> Type*} {l : ι -> Filter α}
  proof: by
  refine ⟨fun t => ⟨fun ht => ?_, ?_⟩⟩
  · rcases (HasBasis.iInf' hl).mem_iff.mp ht with ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    exact ⟨⟨I, fun i => f i⟩, ⟨hI, Subtype.forall.mpr hf⟩, trans (iInter_subtype _ _) hsub⟩
  · rintro ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    grw [← hsub]
    cases hI.nonempty_fintype
exact iI

中文:
定理 HasBasis.iInf
  结论: {ι : 类型} {ι' : ι -> 类型} {l : ι -> Filter α}
  证明: by
  refine ⟨fun t => ⟨fun ht => ?_, ?_⟩⟩
  · rcases (HasBasis.iInf' hl).mem_iff.mp ht with ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    exact ⟨⟨I, fun i => f i⟩, ⟨hI, Subtype.forall.mpr hf⟩, trans (iInter_subtype _ _) hsub⟩
  · rintro ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    grw [← hsub]
    cases hI.nonempty_fintype
exact iI
-/
protected theorem HasBasis.iInf {ι : Type*} {ι' : ι -> Type*} {l : ι -> Filter α}
    {p : forall i, ι' i -> Prop} {s : forall i, ι' i -> Set α} (hl : forall i, (l i).HasBasis (p i) (s i)) :
    (⨅ i, l i).HasBasis
      (fun If : Σ I : Set ι, forall i : I, ι' i => If.1.Finite ∧ forall i : If.1, p i (If.2 i)) fun If =>
      ⋂ i : If.1, s i (If.2 i) := by
  refine ⟨fun t => ⟨fun ht => ?_, ?_⟩⟩
  · rcases (HasBasis.iInf' hl).mem_iff.mp ht with ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    exact ⟨⟨I, fun i => f i⟩, ⟨hI, Subtype.forall.mpr hf⟩, trans (iInter_subtype _ _) hsub⟩
  · rintro ⟨⟨I, f⟩, ⟨hI, hf⟩, hsub⟩
    grw [← hsub]
    cases hI.nonempty_fintype
exact iInter_mem.2 fun i => mem_iInf_of_mem ↑i (hl i).mem_of_mem hf _

open scoped Function in -- required for scoped `on` notation
/--
theorem `_root_.Pairwise.exists_mem_filter_basis_of_disjoint` / 定理 `_root_.Pairwise.exists_mem_filter_basis_of_disjoint`

English:
theorem _root_.Pairwise.exists_mem_filter_basis_of_disjoint
  statement: {I} [Finite I] {l : I -> Filter α}
  proof: by
  rcases hd.exists_mem_filter_of_disjoint with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono fun i j hij => hij.mono (ht _) (ht _)⟩

中文:
定理 _root_.Pairwise.exists_mem_filter_basis_of_disjoint
  结论: {I} [Finite I] {l : I -> Filter α}
  证明: by
  rcases hd.exists_mem_filter_of_disjoint with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono fun i j hij => hij.mono (ht _) (ht _)⟩

Depends on / 依赖: exists_mem_filter_of_disjoint, hd.exists_mem_filter_of_disjoint, hd.mono, hij.mono, mem_iff
-/
theorem _root_.Pairwise.exists_mem_filter_basis_of_disjoint {I} [Finite I] {l : I -> Filter α}
    {ι : I -> Sort*} {p : forall i, ι i -> Prop} {s : forall i, ι i -> Set α} (hd : Pairwise (Disjoint on l))
    (h : forall i, (l i).HasBasis (p i) (s i)) :
    exists ind : forall i, ι i, (forall i, p i (ind i)) ∧ Pairwise (Disjoint on fun i => s i (ind i)) := by
  rcases hd.exists_mem_filter_of_disjoint with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono fun i j hij => hij.mono (ht _) (ht _)⟩

/--
theorem `_root_.Set.PairwiseDisjoint.exists_mem_filter_basis` / 定理 `_root_.Set.PairwiseDisjoint.exists_mem_filter_basis`

English:
theorem _root_.Set.PairwiseDisjoint.exists_mem_filter_basis
  statement: {I : Type*} {l : I -> Filter α}
  proof: by
  rcases hd.exists_mem_filter hS with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono ht⟩

中文:
定理 _root_.Set.PairwiseDisjoint.exists_mem_filter_basis
  结论: {I : 类型} {l : I -> Filter α}
  证明: by
  rcases hd.exists_mem_filter hS with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono ht⟩

Depends on / 依赖: exists_mem_filter, hd.exists_mem_filter, hd.mono, mem_iff
-/
theorem _root_.Set.PairwiseDisjoint.exists_mem_filter_basis {I : Type*} {l : I -> Filter α}
    {ι : I -> Sort*} {p : forall i, ι i -> Prop} {s : forall i, ι i -> Set α} {S : Set I}
    (hd : S.PairwiseDisjoint l) (hS : S.Finite) (h : forall i, (l i).HasBasis (p i) (s i)) :
    exists ind : forall i, ι i, (forall i, p i (ind i)) ∧ S.PairwiseDisjoint fun i => s i (ind i) := by
  rcases hd.exists_mem_filter hS with ⟨t, htl, hd⟩
  choose ind hp ht using fun i => (h i).mem_iff.1 (htl i)
  exact ⟨ind, hp, hd.mono ht⟩

/--
theorem `hasBasis_iInf_principal_finite` / 定理 `hasBasis_iInf_principal_finite`

English:
theorem hasBasis_iInf_principal_finite
  given: {ι : Type*} (s : ι -> Set α)
  proof: by
  refine ⟨fun U => (mem_iInf_finite _).trans ?_⟩
  simp only [iInf_principal_finset, mem_principal,
    exists_finite_iff_finset, Finset.set_biInter_coe]

中文:
定理 hasBasis_iInf_principal_finite
  条件: {ι : 类型} (s : ι -> Set α)
  证明: by
  refine ⟨fun U => (mem_iInf_finite _).trans ?_⟩
  simp only [iInf_principal_finset, mem_principal,
    exists_finite_iff_finset, Finset.set_biInter_coe]

Depends on / 依赖: Finset, Finset.set_biInter_coe, exists_finite_iff_finset, iInf_principal_finset, mem_iInf_finite, mem_principal, set_biInter_coe
-/
theorem hasBasis_iInf_principal_finite {ι : Type*} (s : ι -> Set α) :
    (⨅ i, 𝓟 (s i)).HasBasis (fun t : Set ι => t.Finite) fun t => ⋂ i in t, s i := by
  refine ⟨fun U => (mem_iInf_finite _).trans ?_⟩
  simp only [iInf_principal_finset, mem_principal,
    exists_finite_iff_finset, Finset.set_biInter_coe]

end SameType

end Filter
