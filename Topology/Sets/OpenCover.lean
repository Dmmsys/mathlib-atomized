/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Topology.Sets.Opens

/-!
# Open covers

We define `IsOpenCover` as a predicate on indexed families of open sets in a topological space `X`,
asserting that their union is `X`. This is an example of a declaration whose name is actually
longer than its content; but giving it a name serves as a way of standardizing API.
-/

@[expose] public section

open Set Topology

namespace TopologicalSpace

/--
Definition of `IsOpenCover` / `IsOpenCover` 的定义

English:
definition IsOpenCover
  signature: {ι X : Type*} [TopologicalSpace X] (u : ι -> Opens X)
  body: iSup u = ⊤

中文:
定义 IsOpenCover
  签名: {ι X : 类型} [拓扑空间 X] (u : ι -> Opens X)
  定义体: iSup u = ⊤
-/
def IsOpenCover {ι X : Type*} [TopologicalSpace X] (u : ι -> Opens X) : Prop :=
  iSup u = ⊤

variable {ι κ X Y : Type*} [TopologicalSpace X] {u : ι -> Opens X}
  [TopologicalSpace Y] {v : κ -> Opens Y}

namespace IsOpenCover

/--
lemma `mk` / 引理 `mk`

English:
lemma mk
  given: (h : iSup u = ⊤)
  statement: IsOpenCover u
  proof: h

中文:
引理 mk
  条件: (h : iSup u = ⊤)
  结论: IsOpenCover u
  证明: h
-/
lemma mk (h : iSup u = ⊤) : IsOpenCover u := h

/--
lemma `of_sets` / 引理 `of_sets`

English:
lemma of_sets
  given: {v : ι -> Set X} (h_open : forall i, IsOpen (v i)) (h_iUnion : ⋃ i, v i = univ)
  proof: by
  simp [IsOpenCover, h_iUnion]

中文:
引理 of_sets
  条件: {v : ι -> 集合 X} (h_open : 对任意 i, 是开集 (v i)) (h_iUnion : ⋃ i, v i = univ)
  证明: by
  simp [IsOpenCover, h_iUnion]

Depends on / 依赖: IsOpenCover, h_iUnion
-/
lemma of_sets {v : ι -> Set X} (h_open : forall i, IsOpen (v i)) (h_iUnion : ⋃ i, v i = univ) :
    IsOpenCover (fun i => ⟨v i, h_open i⟩) := by
  simp [IsOpenCover, h_iUnion]

/--
lemma `iSup_eq_top` / 引理 `iSup_eq_top`

English:
lemma iSup_eq_top
  given: (hu : IsOpenCover u)
  statement: ⨆ i, u i = ⊤
  proof: hu

中文:
引理 iSup_eq_top
  条件: (hu : IsOpenCover u)
  结论: ⨆ i, u i = ⊤
  证明: hu
-/
lemma iSup_eq_top (hu : IsOpenCover u) : ⨆ i, u i = ⊤ := hu

/--
lemma `iSup_set_eq_univ` / 引理 `iSup_set_eq_univ`

English:
lemma iSup_set_eq_univ
  given: (hu : IsOpenCover u)
  statement: ⋃ i, (u i : Set X) = univ
  proof: by
  simpa [← SetLike.coe_set_eq] using hu.iSup_eq_top

中文:
引理 iSup_set_eq_univ
  条件: (hu : IsOpenCover u)
  结论: ⋃ i, (u i : 集合 X) = univ
  证明: by
  simpa [← SetLike.coe_set_eq] using hu.iSup_eq_top

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq, hu.iSup_eq_top, iSup_eq_top
-/
lemma iSup_set_eq_univ (hu : IsOpenCover u) : ⋃ i, (u i : Set X) = univ := by
  simpa [← SetLike.coe_set_eq] using hu.iSup_eq_top

/--
lemma `comap` / 引理 `comap`

English:
lemma comap
  given: (hv : IsOpenCover v) (f : C(X, Y))
  statement: IsOpenCover fun k => (v k).comap f
  proof: by
  simp [IsOpenCover, ← preimage_iUnion, hv.iSup_set_eq_univ]

中文:
引理 comap
  条件: (hv : IsOpenCover v) (f : C(X, Y))
  结论: IsOpenCover fun k => (v k).comap f
  证明: by
  simp [IsOpenCover, ← preimage_iUnion, hv.iSup_set_eq_univ]

Depends on / 依赖: IsOpenCover, hv.iSup_set_eq_univ, iSup_set_eq_univ, preimage_iUnion
-/
lemma comap (hv : IsOpenCover v) (f : C(X, Y)) : IsOpenCover fun k => (v k).comap f := by
  simp [IsOpenCover, ← preimage_iUnion, hv.iSup_set_eq_univ]

/--
lemma `exists_mem` / 引理 `exists_mem`

English:
lemma exists_mem
  given: (hu : IsOpenCover u) (a : X)
  statement: exists i, a in u i
  proof: by
  simpa [← hu.iSup_set_eq_univ] using mem_univ a

中文:
引理 存在_mem
  条件: (hu : IsOpenCover u) (a : X)
  结论: 存在 i, a in u i
  证明: by
  simpa [← hu.iSup_set_eq_univ] using mem_univ a

Depends on / 依赖: hu.iSup_set_eq_univ, iSup_set_eq_univ, mem_univ
-/
lemma exists_mem (hu : IsOpenCover u) (a : X) : exists i, a in u i := by
  simpa [← hu.iSup_set_eq_univ] using mem_univ a

/--
lemma `exists_mem_nhds` / 引理 `exists_mem_nhds`

English:
lemma exists_mem_nhds
  given: (hu : IsOpenCover u) (a : X)
  statement: exists i, (u i : Set X) in 𝓝 a
  proof: match hu.exists_mem a with | ⟨i, hi⟩ => ⟨i, (u i).isOpen.mem_nhds hi⟩

中文:
引理 存在_mem_nhds
  条件: (hu : IsOpenCover u) (a : X)
  结论: 存在 i, (u i : 集合 X) in 𝓝 a
  证明: match hu.exists_mem a with | ⟨i, hi⟩ => ⟨i, (u i).isOpen.mem_nhds hi⟩

Depends on / 依赖: exists_mem, hu.exists_mem, isOpen, isOpen.mem_nhds, mem_nhds
-/
lemma exists_mem_nhds (hu : IsOpenCover u) (a : X) : exists i, (u i : Set X) in 𝓝 a :=
  match hu.exists_mem a with | ⟨i, hi⟩ => ⟨i, (u i).isOpen.mem_nhds hi⟩

/--
lemma `iUnion_inter` / 引理 `iUnion_inter`

English:
lemma iUnion_inter
  given: (hu : IsOpenCover u) (s : Set X)
  proof: by
  simp [← inter_iUnion, hu.iSup_set_eq_univ]

中文:
引理 iUnion_inter
  条件: (hu : IsOpenCover u) (s : 集合 X)
  证明: by
  simp [← inter_iUnion, hu.iSup_set_eq_univ]

Depends on / 依赖: hu.iSup_set_eq_univ, iSup_set_eq_univ, inter_iUnion
-/
lemma iUnion_inter (hu : IsOpenCover u) (s : Set X) :
    ⋃ i, s inter u i = s := by
  simp [← inter_iUnion, hu.iSup_set_eq_univ]

/--
lemma `isTopologicalBasis` / 引理 `isTopologicalBasis`

English:
lemma isTopologicalBasis
  statement: (hu : IsOpenCover u)
  proof: isTopologicalBasis_of_cover (fun i => (u i).2) hu.iSup_set_eq_univ hB

中文:
引理 isTopologicalBasis
  结论: (hu : IsOpenCover u)
  证明: isTopologicalBasis_of_cover (fun i => (u i).2) hu.iSup_set_eq_univ hB

Depends on / 依赖: hu.iSup_set_eq_univ, iSup_set_eq_univ, isTopologicalBasis_of_cover
-/
lemma isTopologicalBasis (hu : IsOpenCover u)
    {B : forall i, Set (Set (u i))} (hB : forall i, IsTopologicalBasis (B i)) :
    IsTopologicalBasis (⋃ i, (Subtype.val '' ·) '' B i) :=
  isTopologicalBasis_of_cover (fun i => (u i).2) hu.iSup_set_eq_univ hB

/--
lemma `exists_finite_of_compactSpace` / 引理 `exists_finite_of_compactSpace`

English:
lemma exists_finite_of_compactSpace
  given: (hu : IsOpenCover u) [CompactSpace X]
  proof: by
  rw [IsOpenCover]; rw [eq_top_iff]; rw [← SetLike.coe_subset_coe] at hu
  obtain ⟨s, hs⟩ := IsCompact.elim_finite_subcover isCompact_univ _ (fun i => (u i).2)
    (by simpa using hu)
  use s
  simpa [IsOpenCover, eq_top_iff, ← SetLike.coe_subset_coe, Set.iUnion_subtype] using hs

中文:
引理 存在_finite_of_compactSpace
  条件: (hu : IsOpenCover u) [紧空间 X]
  证明: by
  rw [IsOpenCover]; rw [eq_top_iff]; rw [← SetLike.coe_subset_coe] at hu
  obtain ⟨s, hs⟩ := IsCompact.elim_finite_subcover isCompact_univ _ (fun i => (u i).2)
    (by simpa using hu)
  use s
  simpa [IsOpenCover, eq_top_iff, ← SetLike.coe_subset_coe, Set.iUnion_subtype] using hs

Depends on / 依赖: IsCompact, IsCompact.elim_finite_subcover, IsOpenCover, Set.iUnion_subtype, SetLike, SetLike.coe_subset_coe, coe_subset_coe, elim_finite_subcover, eq_top_iff, iUnion_subtype, isCompact_univ
-/
lemma exists_finite_of_compactSpace (hu : IsOpenCover u) [CompactSpace X] :
    exists (s : Finset ι), IsOpenCover (fun i : s => u i.1) := by
  rw [IsOpenCover]; rw [eq_top_iff]; rw [← SetLike.coe_subset_coe] at hu
  obtain ⟨s, hs⟩ := IsCompact.elim_finite_subcover isCompact_univ _ (fun i => (u i).2)
    (by simpa using hu)
  use s
  simpa [IsOpenCover, eq_top_iff, ← SetLike.coe_subset_coe, Set.iUnion_subtype] using hs

end IsOpenCover

/--
lemma `Opens.IsBasis.isOpenCover` / 引理 `Opens.IsBasis.isOpenCover`

English:
lemma Opens.IsBasis.isOpenCover
  given: {S : Set (Opens X)} (hS : Opens.IsBasis S)
  proof: by
  ext1
  simp [← hS.2]

中文:
引理 Opens.是基.isOpenCover
  条件: {S : 集合 (Opens X)} (hS : Opens.是基 S)
  证明: by
  ext1
  simp [← hS.2]
-/
lemma Opens.IsBasis.isOpenCover {S : Set (Opens X)} (hS : Opens.IsBasis S) :
    IsOpenCover (fun U : S => (U : Opens X)) := by
  ext1
  simp [← hS.2]

/--
lemma `Opens.IsBasis.isOpenCover_mem_and_le` / 引理 `Opens.IsBasis.isOpenCover_mem_and_le`

English:
lemma Opens.IsBasis.isOpenCover_mem_and_le
  statement: {S : Set (Opens X)} (hS : Opens.IsBasis S)
  proof: by
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨i, hxi⟩ := hU.exists_mem x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := hS.exists_subset_of_mem_open hxi (U i).2
  simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.mem_mk, Set.mem_iUnion, SetLike.mem_coe]
  exact ⟨⟨(V, i), hV, hVU⟩, hxV⟩

中文:
引理 Opens.是基.isOpenCover_mem_and_le
  结论: {S : 集合 (Opens X)} (hS : Opens.是基 S)
  证明: by
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨i, hxi⟩ := hU.exists_mem x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := hS.exists_subset_of_mem_open hxi (U i).2
  simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.mem_mk, Set.mem_iUnion, SetLike.mem_coe]
  exact ⟨⟨(V, i), hV, hVU⟩, hxV⟩

Depends on / 依赖: Opens.carrier_eq_coe, Opens.iSup_mk, Opens.mem_mk, Set.mem_iUnion, SetLike, SetLike.mem_coe, carrier_eq_coe, exists_mem, exists_subset_of_mem_open, hS.exists_subset_of_mem_open, hU.exists_mem, iSup_mk, mem_coe, mem_iUnion, mem_mk, top_le_iff, top_le_iff.mp
-/
lemma Opens.IsBasis.isOpenCover_mem_and_le {S : Set (Opens X)} (hS : Opens.IsBasis S)
    {U : ι -> Opens X} (hU : IsOpenCover U) :
    IsOpenCover (fun V : { x : Opens X × ι // x.1 in S ∧ x.1 <= U x.2 } => V.1.1) := by
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨i, hxi⟩ := hU.exists_mem x
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := hS.exists_subset_of_mem_open hxi (U i).2
  simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.mem_mk, Set.mem_iUnion, SetLike.mem_coe]
  exact ⟨⟨(V, i), hV, hVU⟩, hxV⟩

end TopologicalSpace

section Irreducible

open TopologicalSpace Function

/--
theorem `IsPreirreducible.of_subset_iUnion` / 定理 `IsPreirreducible.of_subset_iUnion`

English:
theorem IsPreirreducible.of_subset_iUnion
  statement: {X ι : Type*} [TopologicalSpace X]
  proof: by
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [he]; exact isPreirreducible_empty
  · choose x hx using hne
choose i hi using mem_iUnion.mp hsU hx
    rcases exists_mem_irreducibleComponents_subset_of_isIrreducible (U i).carrier ⟨⟨x, hi⟩, h i⟩
      with ⟨u, hu, hUu⟩
    by_cases huniv : s 

中文:
定理 IsPreirreducible.of_subset_iUnion
  结论: {X ι : 类型} [拓扑空间 X]
  证明: by
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [he]; exact isPreirreducible_empty
  · choose x hx using hne
choose i hi using mem_iUnion.mp hsU hx
    rcases exists_mem_irreducibleComponents_subset_of_isIrreducible (U i).carrier ⟨⟨x, hi⟩, h i⟩
      with ⟨u, hu, hUu⟩
    by_cases huniv : s 

Depends on / 依赖: IsClosed, IsClosed.isOpen_compl, IsOpen, carrier, eq_empty_or_nonempty, exists_mem_irreducibleComponents_subset_of_isIrreducible, isClosed_of_mem_irreducibleComponents, isOpen_compl, isPreirreducible_empty, mem_i, mem_iUnion, mem_iUnion.mp, not_subset, not_subset.mp, open_subset, s.eq_empty_or_nonempty, subseteq
-/
theorem IsPreirreducible.of_subset_iUnion {X ι : Type*} [TopologicalSpace X]
    {U : ι -> Opens X} (hn : Pairwise ((¬ Disjoint · ·) on U))
    (h : forall i, IsPreirreducible ((U i) : Set X))
    {s : Set X} (hs : IsOpen s) (hsU : s subseteq ⋃ i, U i) :
    IsPreirreducible s := by
  rcases s.eq_empty_or_nonempty with he | hne
  · rw [he]; exact isPreirreducible_empty
  · choose x hx using hne
choose i hi using mem_iUnion.mp hsU hx
    rcases exists_mem_irreducibleComponents_subset_of_isIrreducible (U i).carrier ⟨⟨x, hi⟩, h i⟩
      with ⟨u, hu, hUu⟩
    by_cases huniv : s subseteq u
    · exact hu.1.2.open_subset hs huniv
    · have huo : IsOpen uᶜ :=
        IsClosed.isOpen_compl (self := isClosed_of_mem_irreducibleComponents u hu)
      rcases not_subset.mp huniv with ⟨a, ⟨ha₁, ha₂⟩⟩
choose j haj using mem_iUnion.mp hsU ha₁
have hji : j != i := fun hji' => ha₂ hUu hji' ▸ haj
      rcases inter_nonempty_iff_exists_left.mp
        ((h j) (U i) uᶜ (U i).isOpen huo
        (not_disjoint_iff_nonempty_inter.mp (by simpa using hn hji)) ⟨a, ⟨haj, ha₂⟩⟩).right
        with ⟨x, hx₁, hx₂⟩
exfalso; exact hx₂ hUu hx₁

/--
theorem `PreirreducibleSpace.of_isOpenCover` / 定理 `PreirreducibleSpace.of_isOpenCover`

English:
theorem PreirreducibleSpace.of_isOpenCover
  statement: {X ι : Type*} [TopologicalSpace X]
  proof: have h' (i : _) : IsPreirreducible (U i).carrier := IsPreirreducible.of_subtype
  ⟨IsPreirreducible.of_subset_iUnion hn h' isOpen_univ (by simpa using hU.iSup_set_eq_univ)⟩

中文:
定理 Preirreducible空间.of_isOpenCover
  结论: {X ι : 类型} [拓扑空间 X]
  证明: have h' (i : _) : IsPreirreducible (U i).carrier := IsPreirreducible.of_subtype
  ⟨IsPreirreducible.of_subset_iUnion hn h' isOpen_univ (by simpa using hU.iSup_set_eq_univ)⟩

Depends on / 依赖: IsPreirreducible, IsPreirreducible.of_subset_iUnion, IsPreirreducible.of_subtype, carrier, hU.iSup_set_eq_univ, iSup_set_eq_univ, isOpen_univ, of_subset_iUnion, of_subtype
-/
theorem PreirreducibleSpace.of_isOpenCover {X ι : Type*} [TopologicalSpace X]
    {U : ι -> Opens X} (hn : Pairwise ((¬ Disjoint · ·) on U)) (hU : IsOpenCover U)
    (h : forall i, PreirreducibleSpace (U i)) :
    PreirreducibleSpace X :=
  have h' (i : _) : IsPreirreducible (U i).carrier := IsPreirreducible.of_subtype
  ⟨IsPreirreducible.of_subset_iUnion hn h' isOpen_univ (by simpa using hU.iSup_set_eq_univ)⟩

end Irreducible
